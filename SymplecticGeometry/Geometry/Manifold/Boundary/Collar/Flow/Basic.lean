/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.Flow.Local
public import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.Local
public import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.Opens
public import SymplecticGeometry.Topology.Compactness.SigmaCompact
public import TauCeti.Geometry.Manifold.Boundary.Collar.Smooth
public import TauCeti.Geometry.Manifold.Boundary.OutwardExistence
public import TauCeti.Geometry.Manifold.IntegralCurve.Interval
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions

/-!
# The collar of a compact boundary along an outward field

Let `W` be a Hausdorff manifold modelled on the half-space `𝓡∂ (n + 1)`, with compact boundary
`∂W`, and `Y` a smooth vector field on `W` pointing out of `W` along `∂W`
(`TauCeti.IsOutwardPointingField`). This file builds a smooth collar of `∂W` out of the backward
integral curves of `Y` from the boundary points: for some `ε > 0`, the map
`c (x, t) = Φ (-ε t, x)` on `∂W × [0, 1)` is a `TauCeti.SmoothCollar`, where `s ↦ Φ (s, x)` is
the integral curve of `Y` on `(-ε, 0]` that ends at `x`.

The proof patches the local construction of `Flow/Local.lean`. Near each boundary point,
`TauCeti.exists_isMIntegralCurveOn_of_isOutwardPointing` gives the integral curves from an open
piece of the boundary for some positive time, and their flow map is a local diffeomorphism there.
Finitely many pieces cover the compact boundary, which gives a common time; the curves of
overlapping pieces agree by uniqueness (Tau Ceti's `IsMIntegralCurveOn.eqOn_of_isPreconnected`,
on the interval `(-η, 0]`, for the smooth field `Y`), so the
patched flow map is a local diffeomorphism on `∂W × [0, η)`. It is the inclusion on `∂W × {0}`,
so it is injective on an open neighbourhood of `∂W × {0}`
(`Set.InjOn.exists_isOpen_superset_isLocalDiffeomorphOn`), which by the tube lemma contains a
product `∂W × [0, ε)`. Rescaling `[0, 1)` to `[0, ε)` gives the collar. This last part uses no
flow, and is stated on its own as `TauCeti.SmoothCollar.exists_eq_of_isLocalDiffeomorphOn`; it
adapts the proof of Tau Ceti's `TauCeti.exists_pos_injOn_flowOf_comp`, the uniform width of the
Liouville collar of a compact hypersurface, from the time interval `(-ε, ε)` of a boundaryless
manifold to the half-open interval of a boundary.

On a σ-compact manifold, outward fields exist (Tau Ceti's
`TauCeti.exists_isOutwardPointingField`, by a partition of unity). A compact boundary has a
σ-compact open neighbourhood `V`, since `W` is locally compact
(`IsCompact.exists_isOpen_isSigmaCompact_subset`), and a collar of `∂V` is a collar of `∂W`
(`TauCeti.SmoothCollar.ofOpens`). So every compact boundary of a Hausdorff manifold has a smooth
collar, inside any given open neighbourhood of the boundary, without σ-compactness of `W`.

## Main results

* `TauCeti.SmoothCollar.exists_eq_of_isOutwardPointing`: a smooth collar whose normal lines,
  run at speed `ε`, are the integral curves of an outward field through the boundary points.
* `TauCeti.SmoothCollar.exists_eq_of_isOutwardPointing_of_subset`: the same, with the image of
  the collar inside a given open neighbourhood of the boundary.
* `TauCeti.SmoothCollar.exists_range_subset` and the instance `Nonempty (SmoothCollar n ∞ W)`:
  a compact boundary of a Hausdorff manifold has a smooth collar, which may be taken
  inside any open neighbourhood of the boundary.
* `TauCeti.SmoothCollar.exists_eq_of_isLocalDiffeomorphOn`: a local diffeomorphism from
  `∂W × [0, η)` that is the inclusion on `∂W × {0}` gives, after rescaling, a smooth collar.
* `TauCeti.SmoothCollar.apply_normalIioRay_eq` and
  `TauCeti.SmoothCollar.contMDiffOn_of_forall_apply_eq`: when `c (x, t) = Φ (-ε t, x)`, the point
  `Φ (s, x)` for `s ∈ (-ε, 0]` is the point of `c` at depth `-s / ε`, and `Φ` is smooth on
  `(-ε, 0) × ∂W`.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33, 1976, Chapter 4, Theorem 6.1.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218, 2013, Theorem 9.25.
-/

public section

open Set Filter Function Topology SymplecticGeometry
open scoped Manifold ContDiff

namespace TauCeti

open _root_.TauCeti.EuclideanHalfSpace SymplecticGeometry.EuclideanHalfSpace

namespace SmoothCollar

variable {n : ℕ} {W : Type*} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
  [IsManifold (𝓡∂ (n + 1)) ∞ W] [T2Space W] {Y : (x : W) → TangentSpace (𝓡∂ (n + 1)) x}

/-- The local integral curves of `exists_isMIntegralCurveOn_of_isOutwardPointing` patch, over a
compact boundary, to integral curves from every boundary point with a common time `η`, whose flow
map from the boundary is a local diffeomorphism on `∂W × [0, η)`. -/
private theorem exists_isLocalDiffeomorphOn_of_isOutwardPointing
    [CompactSpace ↥((𝓡∂ (n + 1)).boundary W)] (hY : IsOutwardPointingField Y) :
    ∃ (η : ℝ) (Φ : ℝ × (𝓡∂ (n + 1)).boundary W → W), 0 < η ∧ (∀ x, Φ (0, x) = x) ∧
      (∀ x, IsMIntegralCurveOn (fun s ↦ Φ (s, x)) Y (Ioc (-η) 0)) ∧
      IsLocalDiffeomorphOn ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) ∞
        (fun q : (𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1 ↦ Φ (-q.2.val 0, q.1))
        (univ ×ˢ normalIio η) := by
  choose B η γ hBo hpB hη hγ0 _ hγY hγloc using
    exists_isMIntegralCurveOn_of_isOutwardPointing hY
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover B fun p ↦ (hBo p).mem_nhds (hpB p)
  have hcov : ∀ x, ∃ p ∈ t, x ∈ B p := fun x ↦ by
    simpa using (ht.symm ▸ mem_univ x : x ∈ ⋃ p ∈ t, B p)
  choose i hit hxi using hcov
  -- A common time, below the times of the finitely many local pieces.
  obtain ⟨η₀, hη₀le, hη₀⟩ : ∃ η₀, (∀ p ∈ t, η₀ ≤ η p) ∧ 0 < η₀ :=
    (((eventually_all_finset t).2 fun p _ ↦
      (eventually_le_nhds (hη p)).filter_mono nhdsWithin_le_nhds).and
      self_mem_nhdsWithin).exists (f := 𝓝[>] (0 : ℝ))
  have hsub : ∀ x, Ioc (-η₀) 0 ⊆ Ioc (-η (i x)) 0 := fun x ↦
    Ioc_subset_Ioc_left (neg_le_neg (hη₀le _ (hit x)))
  refine ⟨η₀, fun q ↦ γ (i q.2) q, hη₀, fun x ↦ hγ0 _ x (hxi x),
    fun x ↦ (hγY _ x (hxi x)).mono (hsub x), ?_⟩
  rintro ⟨⟨x, s⟩, -, hs⟩
  -- Near `(x, s)`, the patched map is the local piece around `x`, by uniqueness of the curves.
  have heq : EqOn
      (fun q : (𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1 ↦ γ (i x) (-q.2.val 0, q.1))
      (fun q ↦ γ (i q.1) (-q.2.val 0, q.1)) (B (i x) ×ˢ normalIio η₀) := by
    rintro ⟨y, r⟩ ⟨hy, hr⟩
    have hr' : -r.val 0 ∈ Ioc (-η₀) 0 :=
      ⟨neg_lt_neg (mem_normalIio.1 hr), neg_nonpos.2 r.property⟩
    exact IsMIntegralCurveOn.eqOn_of_isPreconnected ((hγY _ y hy).mono (hsub x))
      ((hγY _ y (hxi y)).mono (hsub y)) isPreconnected_Ioc ⟨by linarith, le_rfl⟩
      (fun _ _ ↦ ((isOutwardPointingField_iff.1 hY).1.of_le (by simp)).contMDiffAt)
      (by simp only [hγ0 _ y hy, hγ0 _ y (hxi y)]) hr'
  have hmem : B (i x) ×ˢ normalIio η₀ ∈ 𝓝 (x, s) :=
    ((hBo _).prod (isOpen_normalIio _)).mem_nhds ⟨hxi x, hs⟩
  exact (hγloc (i x) ⟨(x, s), hxi x,
    mem_normalIio.2 ((mem_normalIio.1 hs).trans_le (hη₀le _ (hit x)))⟩).congr_of_eventuallyEq
    (Filter.EventuallyEq.symm (eventually_of_mem hmem heq))

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
/-- **A collar from a local diffeomorphism that is the inclusion on the boundary.** Let `W` be a
Hausdorff manifold modelled on the half-space, with compact boundary `∂W`, `U` an open set
containing `∂W`, and `F : ∂W × EuclideanHalfSpace 1 → W` a `C^k` local diffeomorphism on
`∂W × [0, η)`, for some `η > 0`, with `F (x, 0) = x`. Then for some `0 < ε ≤ η` the map
`c (x, t) = F (x, normalRay (ε t))`, that is `F (x, ε t)`, on `∂W × [0, 1)` is a `C^k` collar
with image in `U`.

The proof adapts that of Tau Ceti's `TauCeti.exists_pos_injOn_flowOf_comp` from the interval
`(-ε, ε)` to the half-open interval `[0, ε)`. -/
theorem exists_eq_of_isLocalDiffeomorphOn [CompactSpace ↥((𝓡∂ (n + 1)).boundary W)]
    {k : WithTop ℕ∞} {η : ℝ}
    (hη : 0 < η) {F : (𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1 → W}
    (hF : IsLocalDiffeomorphOn ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) k F (univ ×ˢ normalIio η))
    (hF0 : ∀ x, F (x, 0) = x) {U : Set W} (hU : IsOpen U)
    (hbU : (𝓡∂ (n + 1)).boundary W ⊆ U) :
    ∃ ε, 0 < ε ∧ ε ≤ η ∧ ∃ c : SmoothCollar n k W,
      (∀ q, c q = F (q.1, normalRay (ε * (q.2 : EuclideanHalfSpace 1).val 0))) ∧ range c ⊆ U := by
  -- On `∂W × {0}` the map `F` is the inclusion, so it is injective there, and hence injective
  -- and a local diffeomorphism on an open neighbourhood `O` of `∂W × {0}`.
  set K : Set ((𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1) := univ ×ˢ {0}
  have hKη : K ⊆ univ ×ˢ normalIio η :=
    prod_mono subset_rfl (singleton_subset_iff.2 (zero_mem_normalIio hη))
  obtain ⟨O, hOo, hKO, hinj, hlocO⟩ := Set.InjOn.exists_isOpen_superset_isLocalDiffeomorphOn
    (f := F) (K := K)
    (by
      rintro ⟨a, _⟩ ⟨-, rfl⟩ ⟨b, _⟩ ⟨-, rfl⟩ h
      rw [hF0, hF0] at h
      rw [Subtype.ext h])
    (isCompact_univ.prod isCompact_singleton) fun q hq ↦ hF ⟨q, hKη hq⟩
  -- By the tube lemma, the open set `O ∩ F ⁻¹' U` contains a collar of uniform width.
  have hVo : IsOpen (O ∩ F ⁻¹' U) := hlocO.contMDiffOn.continuousOn.isOpen_inter_preimage hOo hU
  have hKV : K ⊆ O ∩ F ⁻¹' U := fun q hq ↦ ⟨hKO hq, by
    obtain ⟨x, t⟩ := q
    obtain rfl : t = 0 := mem_singleton_iff.1 hq.2
    simpa [hF0] using hbU x.property⟩
  obtain ⟨_, v, -, hv, hu, h0v, huv⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hVo hKV
  obtain ⟨ε', hε', hε'v⟩ := exists_normalIio_subset hv (h0v rfl)
  set ε := min ε' η
  have hε : 0 < ε := lt_min hε' hη
  have hsubV : univ ×ˢ normalIio ε ⊆ O ∩ F ⁻¹' U := fun q hq ↦
    huv ⟨hu (mem_univ _),
      hε'v (mem_normalIio.2 ((mem_normalIio.1 hq.2).trans_le (min_le_left _ _)))⟩
  -- Rescaling `[0, 1)` to `[0, ε)` gives the collar.
  let σ : EuclideanHalfSpace 1 → EuclideanHalfSpace 1 := fun t ↦
    ⟨ε • t.val, by simpa using mul_nonneg hε.le t.property⟩
  have hσ : ∀ t, (σ t).val = ε • t.val := fun _ ↦ rfl
  let ψ : (𝓡∂ (n + 1)).boundary W × normalIioOpens 1 →
      (𝓡∂ (n + 1)).boundary W × EuclideanHalfSpace 1 :=
    Prod.map id (σ ∘ Subtype.val)
  have hψ : ∀ p, ψ p ∈ univ ×ˢ normalIio ε := fun p ↦ ⟨mem_univ _, by
    simpa [ψ, hσ, mem_normalIio] using
      mul_lt_of_lt_one_right hε (mem_normalIioOpens.1 p.2.property)⟩
  have hψloc : IsLocalDiffeomorph ((𝓡 n).prod (𝓡∂ 1)) ((𝓡 n).prod (𝓡∂ 1)) k ψ :=
    SymplecticGeometry.isLocalDiffeomorph_id.prodMap fun t ↦
      (isLocalDiffeomorph_subtype_val t).comp (hg :=
        (EuclideanHalfSpace.isLocalDiffeomorph_of_val_eq_smul hε hσ _))
  have hψinj : Injective ψ := injective_id.prodMap fun s t h ↦
    Subtype.ext (Subtype.ext (smul_right_injective _ hε.ne' (congrArg Subtype.val h)))
  have hFψ : ∀ p, F (ψ p) = F (p.1, normalRay (ε * (p.2 : EuclideanHalfSpace 1).val 0)) :=
    fun ⟨x, t⟩ ↦ by
      simp only [ψ, Prod.map_apply, id_eq, comp_apply]
      rw [← normalRay_normalCoord (σ t), hσ, PiLp.smul_apply, smul_eq_mul]
  let c : SmoothCollar n k W :=
    { toFun := F ∘ ψ
      isLocalDiffeomorph' := fun p ↦ (hψloc p).comp (hg := hlocO ⟨ψ p, (hsubV (hψ p)).1⟩)
      injective' := fun p q h ↦ hψinj (hinj (hsubV (hψ p)).1 (hsubV (hψ q)).1 h)
      apply_zero' := fun x ↦ by
        rw [comp_apply, hFψ, coe_normalIioOpensZero, val_zero_apply, mul_zero, normalRay_zero,
          hF0] }
  refine ⟨ε, hε, min_le_right _ _, c, hFψ, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact (hsubV (hψ p)).2

/-- **A collar along an outward field, inside a given neighbourhood of the boundary.** Let `W` be
a smooth Hausdorff manifold modelled on the half-space, with compact boundary `∂W`, `Y` a
smooth vector field pointing outward along `∂W`, and `U` an open set containing `∂W`. There are
`ε > 0`, a map `Φ : ℝ × ∂W → W` such that each `s ↦ Φ (s, x)` is an integral curve of `Y` on
`(-ε, 0]` ending at `x`, and a smooth collar `c` with image in `U` whose normal lines are these
curves run at speed `ε`: `c (x, t) = Φ (-ε t, x)`. -/
theorem exists_eq_of_isOutwardPointing_of_subset [CompactSpace ↥((𝓡∂ (n + 1)).boundary W)]
    (hY : IsOutwardPointingField Y) {U : Set W} (hU : IsOpen U)
    (hbU : (𝓡∂ (n + 1)).boundary W ⊆ U) :
    ∃ (ε : ℝ) (Φ : ℝ × (𝓡∂ (n + 1)).boundary W → W) (c : SmoothCollar n ∞ W), 0 < ε ∧
      (∀ x, Φ (0, x) = x) ∧ (∀ x, IsMIntegralCurveOn (fun s ↦ Φ (s, x)) Y (Ioc (-ε) 0)) ∧
      (∀ q, c q = Φ (-ε * (q.2 : EuclideanHalfSpace 1).val 0, q.1)) ∧ range c ⊆ U := by
  obtain ⟨η, Φ, hη, hΦ0, hΦY, hloc⟩ := exists_isLocalDiffeomorphOn_of_isOutwardPointing hY
  obtain ⟨ε, hε, hεη, c, hc, hcU⟩ := exists_eq_of_isLocalDiffeomorphOn hη hloc
    (fun x ↦ by simp [val_zero_apply, hΦ0]) hU hbU
  refine ⟨ε, Φ, c, hε, hΦ0, fun x ↦ (hΦY x).mono (Ioc_subset_Ioc_left (neg_le_neg hεη)),
    fun q ↦ ?_, hcU⟩
  rw [hc q, normalRay_coe_apply,
    max_eq_left (mul_nonneg hε.le (q.2 : EuclideanHalfSpace 1).property), neg_mul]

/-- **A collar along an outward field.** Let `W` be a smooth Hausdorff manifold modelled on
the half-space, with compact boundary `∂W`, and `Y` a smooth vector field pointing outward
along `∂W`. There are `ε > 0`, a map `Φ : ℝ × ∂W → W` such that each `s ↦ Φ (s, x)` is an
integral curve of `Y` on `(-ε, 0]` ending at `x`, and a smooth collar `c` whose normal lines
are these curves run at speed `ε`: `c (x, t) = Φ (-ε t, x)`. -/
theorem exists_eq_of_isOutwardPointing [CompactSpace ↥((𝓡∂ (n + 1)).boundary W)]
    (hY : IsOutwardPointingField Y) :
    ∃ (ε : ℝ) (Φ : ℝ × (𝓡∂ (n + 1)).boundary W → W) (c : SmoothCollar n ∞ W), 0 < ε ∧
      (∀ x, Φ (0, x) = x) ∧ (∀ x, IsMIntegralCurveOn (fun s ↦ Φ (s, x)) Y (Ioc (-ε) 0)) ∧
      ∀ q, c q = Φ (-ε * (q.2 : EuclideanHalfSpace 1).val 0, q.1) := by
  obtain ⟨ε, Φ, c, hε, hΦ0, hΦY, hc, -⟩ :=
    exists_eq_of_isOutwardPointing_of_subset hY isOpen_univ (subset_univ _)
  exact ⟨ε, Φ, c, hε, hΦ0, hΦY, hc⟩

/-- **Smooth collars of compact boundaries.** Let `W` be a smooth Hausdorff manifold modelled on
the half-space, with compact boundary `∂W`, and `U` an open set containing `∂W`. Then `∂W` has a
smooth collar with image in `U`. -/
theorem exists_range_subset [CompactSpace ↥((𝓡∂ (n + 1)).boundary W)]
    {U : Set W} (hU : IsOpen U) (hbU : (𝓡∂ (n + 1)).boundary W ⊆ U) :
    ∃ c : SmoothCollar n ∞ W, range c ⊆ U := by
  have : LocallyCompactSpace W := Manifold.locallyCompact_of_finiteDimensional (𝓡∂ (n + 1))
  obtain ⟨V, hVo, hbV, hVU, hVσ⟩ :=
    (isCompact_iff_compactSpace.2 ‹_›).exists_isOpen_isSigmaCompact_subset hU hbU
  lift V to TopologicalSpace.Opens W using hVo
  have : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.1 hVσ
  have : CompactSpace ↥((𝓡∂ (n + 1)).boundary V) :=
    (diffeomorphBoundaryOpens (k := ∞) V hbV).toHomeomorph.symm.compactSpace
  obtain ⟨Y, hY⟩ := exists_isOutwardPointingField (n := n) (M := V)
  obtain ⟨-, -, c, -, -, -, -⟩ := exists_eq_of_isOutwardPointing hY
  refine ⟨c.ofOpens hbV, ?_⟩
  rw [range_ofOpens]
  exact (image_subset_range _ _).trans (Subtype.range_val.trans_subset hVU)

/-- **Smooth collars of compact boundaries.** A smooth Hausdorff manifold modelled on the
half-space whose boundary is compact has a smooth collar of its boundary. -/
instance instNonempty [CompactSpace ↥((𝓡∂ (n + 1)).boundary W)] :
    Nonempty (SmoothCollar n ∞ W) :=
  (exists_range_subset isOpen_univ (subset_univ ((𝓡∂ (n + 1)).boundary W))).nonempty

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] [T2Space W] in
/-- If the normal lines of a collar `c` are the lines of `Φ` run at speed `ε`,
`c (x, t) = Φ (-ε t, x)`, then for `s ∈ (-ε, 0]` the point `Φ (s, x)` is the point of `c` at
depth `-s / ε` over `x`. -/
theorem apply_normalIioRay_eq {ε : ℝ} (hε : 0 < ε) {Φ : ℝ × (𝓡∂ (n + 1)).boundary W → W}
    {c : SmoothCollar n ∞ W} (hc : ∀ q, c q = Φ (-ε * (q.2 : EuclideanHalfSpace 1).val 0, q.1))
    {s : ℝ} (hs : s ∈ Ioc (-ε) 0) (x : (𝓡∂ (n + 1)).boundary W) :
    c (x, normalIioRay ⟨-s / ε, by rw [mem_Iio, div_lt_one hε]; linarith [hs.1]⟩) = Φ (s, x) := by
  rw [hc, normalIioRay_coe_apply, max_eq_left (div_nonneg (neg_nonneg.2 hs.2) hε.le)]
  congr 2
  field_simp

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] [T2Space W] in
/-- If the normal lines of a collar `c` are the lines of `Φ` run at speed `ε`,
`c (x, t) = Φ (-ε t, x)`, then `Φ` is smooth on `(-ε, 0) × ∂W`: near each of its points it is
`c` composed with a smooth depth map. -/
theorem contMDiffOn_of_forall_apply_eq {ε : ℝ} (hε : 0 < ε)
    {Φ : ℝ × (𝓡∂ (n + 1)).boundary W → W} {c : SmoothCollar n ∞ W}
    (hc : ∀ q, c q = Φ (-ε * (q.2 : EuclideanHalfSpace 1).val 0, q.1)) :
    ContMDiffOn (𝓘(ℝ).prod (𝓡 n)) (𝓡∂ (n + 1)) ∞ Φ (Ioo (-ε) 0 ×ˢ univ) := by
  rintro ⟨t, x⟩ ⟨ht, -⟩
  refine ContMDiffAt.contMDiffWithinAt ?_
  obtain ⟨a, hta, ha⟩ := exists_between (show -t / ε < 1 by rw [div_lt_one hε]; linarith [ht.1])
  have hpos : 0 < -t / ε := div_pos (neg_pos.2 ht.2) hε
  -- The depth `min (-s / ε) a`, which is `-s / ε` near `t`.
  have hd : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) ∞ (fun s : ℝ ↦ min (-s / ε) a) t :=
    (contDiff_id.neg.div_const ε).contMDiff.contMDiffAt.congr_of_eventuallyEq
      ((((continuous_neg.div_const ε).tendsto t).eventually (gt_mem_nhds hta)).mono
        fun s hs ↦ min_eq_left hs.le)
  have hρ := hd.normalIioRay (fun s ↦ (min_le_right _ _).trans_lt ha) (lt_min hpos (hpos.trans hta))
  refine ((c.contMDiff _).comp _ (contMDiffAt_snd.prodMk
    (hρ.comp _ contMDiffAt_fst))).congr_of_eventuallyEq ?_
  have hnhds : Ioo (-(a * ε)) 0 ∈ 𝓝 t :=
    Ioo_mem_nhds (by rw [div_lt_iff₀ hε] at hta; linarith) ht.2
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds hnhds] with q hq
  have hq1 : -q.1 / ε < a := by rw [div_lt_iff₀ hε]; linarith [hq.1]
  rw [← apply_normalIioRay_eq hε hc ⟨by nlinarith [hq.1, ha], hq.2.le⟩ q.2]
  simp only [Function.comp_apply, min_eq_left hq1.le]

end SmoothCollar

end TauCeti

end

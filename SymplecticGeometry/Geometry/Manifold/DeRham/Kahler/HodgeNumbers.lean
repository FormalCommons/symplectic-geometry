/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DeRham.Kahler.Decomposition
public import TauCeti.Geometry.Symplectic.Manifold.Kahler
import SymplecticGeometry.Geometry.Manifold.DeRham.SmoothFamily.GoodCover
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.AlmostComplexType
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Metric
import TauCeti.Geometry.Symplectic.Manifold.Volume

/-!
# Hodge numbers and Betti numbers of closed Kähler manifolds

Let `J` be a smooth almost complex structure on `M`, and write `h^{p,q}` for the complex dimension
of the subspace `H^{p,q}` of `H^k_dR(M; ℂ)`, `TauCeti.complexDeRhamCohomology.hodgePiece J k p q`.
Complex conjugation maps `H^{p,q}` onto `H^{q,p}` conjugate-linearly, so `h^{p,q} = h^{q,p}`, for
every `J`.

Now let `M` be compact, Hausdorff and boundaryless, with `J` integrable and a closed two-form `σ`
compatible with `J`. If `M` is nonempty, `J` makes its dimension even, say `2 n`. Inside the
proofs we equip `M` with the metric `g_J(u, v) = σ(u, J v)`
(`TauCeti.SmoothTwoForm.Compatible.metric`) and with the symplectic orientation of `σ`
(`TauCeti.SmoothTwoForm.IsNondegenerate.volumeOrientation`); the statements depend on neither.
The Hodge star commutes with the derivation of `J`
(`TauCeti.SmoothForm.complexHodgeStar_alternatingDerivation`, in `Kahler/Decomposition.lean`),
so it maps the harmonic forms of type `(p,q)` injectively to those of type `(n - q, n - p)`,
which gives `h^{p,q} = h^{n-q,n-p}` for `p, q ≤ n`. The Hodge decomposition
(`Kahler/Decomposition.lean`) holds in every degree (above the dimension all pieces vanish), and
the Hodge numbers add up to the Betti number `b_k = dim H^k_dR(M; ℝ)`. In odd degree the symmetry
`h^{p,q} = h^{q,p}` pairs the terms of this sum, so the odd Betti numbers are even.

The proof of `finrank_hodgePiece_symm` follows Tau Ceti's
`TauCeti.Hodge.HodgeStructureOn.hodgeNumber_symm` for the pieces `H^{p,q}`, which form a Hodge
structure only on a compact Kähler manifold: conjugation maps `H^{p,q}` onto `H^{q,p}`
(`TauCeti.complexDeRhamCohomology.map_conj_hodgePiece`), and Mathlib's `rank_eq_of_equiv_equiv`
compares the dimensions of spaces related by a semilinear bijection.

## Main results

* `TauCeti.complexDeRhamCohomology.finrank_hodgePiece_symm`: `h^{p,q} = h^{q,p}`.
* `TauCeti.complexDeRhamCohomology.isHodgeDecomposition_hodgePiece_of_compatible`: the Hodge
  decomposition in every degree.
* `TauCeti.complexDeRhamCohomology.finrank_hodgePiece_serre`: `h^{p,q} = h^{n-q,n-p}`.
* `TauCeti.finrank_deRhamCohomology_eq_sum`: `b_k = ∑_{p+q=k} h^{p,q}`.
* `TauCeti.even_finrank_deRhamCohomology_of_odd`: the odd Betti numbers are even.
* `TauCeti.SmoothTwoForm.IsKahler.hodge_decomposition`: these results together, for a closed
  Kähler manifold.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §7.
* [J.-P. Demailly, *Complex Analytic and Differential Geometry*][Demailly2012],
  Chapter VI, Theorem (8.5).
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  (4.3.8).
-/

public section

noncomputable section

open Bundle Module SymplecticGeometry
open scoped ContDiff RealInnerProductSpace

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### Hodge symmetry -/

namespace complexDeRhamCohomology

variable (J : SmoothAlmostComplexStructure I M)

/-- **Hodge symmetry of the Hodge numbers**: for every almost complex structure `J`, the spaces
`H^{p,q}` and `H^{q,p}` of `H^k_dR(M; ℂ)` have the same complex dimension, since complex conjugation
maps one onto the other. -/
theorem finrank_hodgePiece_symm (k p q : ℕ) :
    finrank ℂ (hodgePiece J k p q) = finrank ℂ (hodgePiece J k q p) := by
  rw [← map_conj_hodgePiece J p q]
  exact congrArg Cardinal.toNat (rank_eq_of_equiv_equiv (starRingEnd ℂ)
    ((conj k).toEquiv.submoduleMap _).toAddEquiv
    ⟨RingHom.injective _, fun z ↦ ⟨starRingEnd ℂ z, by simp⟩⟩
    fun r x ↦ ((conj k).toEquiv.submoduleMap _).map_smulₛₗ r x)

end complexDeRhamCohomology

/-! ### Compact Kähler manifolds -/

variable [FiniteDimensional ℝ E] [BoundarylessManifold I M] [T2Space M] [CompactSpace M]

namespace complexDeRhamCohomology

variable {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M} {n : ℕ}

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [T2Space M] [CompactSpace M] in
/-- When complex de Rham cohomology in degree `k` is trivial, its pieces, which all vanish, form a
Hodge decomposition of weight `k`. -/
private theorem isHodgeDecomposition_hodgePiece_of_subsingleton {k : ℕ}
    [Subsingleton (complexDeRhamCohomology I M k)] :
    Hodge.IsHodgeDecomposition (conj k) k
      (fun p : ℤ ↦ hodgePiece J k p.toNat (k - p).toNat) :=
  { isInternal := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (fun i ↦ by simp [Subsingleton.elim (hodgePiece J k _ _) ⊥]) (Subsingleton.elim _ _)
    map_conj := fun _ ↦ Subsingleton.elim _ _
    exists_forall_lt_eq_bot := ⟨0, fun _ _ ↦ Subsingleton.elim _ _⟩ }

/-- **The Hodge decomposition in every degree**: on a compact Hausdorff boundaryless manifold,
with `J` integrable and `σ` a closed two-form compatible with `J`, the subspaces `H^{p,k-p}` form
a Hodge decomposition of weight `k` of `H^k_dR(M; ℂ)`, for every `k`. -/
theorem isHodgeDecomposition_hodgePiece_of_compatible (hσ : σ.IsClosed) (hc : σ.Compatible J)
    (hJ : J.IsIntegrable) (k : ℕ) :
    Hodge.IsHodgeDecomposition (conj k) k
      (fun p : ℤ ↦ hodgePiece J k p.toNat (k - p).toNat) := by
  cases isEmpty_or_nonempty M with
  | inl _ =>
    have : Subsingleton (complexDeRhamCohomology I M k) := (mk_surjective I k).subsingleton
    exact isHodgeDecomposition_hodgePiece_of_subsingleton
  | inr hM =>
    obtain ⟨n, hn⟩ := J.even_finrank hM.some
    rw [← two_mul] at hn
    rcases le_or_gt k (2 * n) with hk | hk
    · let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨hc.metric.toRiemannianMetric⟩
      exact isHodgeDecomposition_hodgePiece (hc.isNondegenerate.volumeOrientation hn) hJ hσ
        hc.inner_eq_eval₂ (Nat.add_sub_cancel' hk)
    · have := subsingleton_deRhamCohomology_of_finrank_lt (I := I) M (hn ▸ hk)
      have : Subsingleton (complexDeRhamCohomology I M k) := by
        rw [← Module.finrank_zero_iff (R := ℂ), finrank_complexDeRhamCohomology,
          Module.finrank_zero_of_subsingleton]
      exact isHodgeDecomposition_hodgePiece_of_subsingleton

/-- With the metric `⟪v, w⟫ = σ(v, J w)` and an orientation, on a manifold of dimension `2 n`,
the space `H^{p,q}` of `H^k_dR(M; ℂ)` has at most the dimension of `H^{n-q,n-p}` in degree
`l = 2 n - k`, for `p, q ≤ n`: the Hodge star maps harmonic forms of type `(p,q)` injectively to
harmonic forms of type `(n - q, n - p)`. -/
private theorem finrank_hodgePiece_le
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (o : Manifold.Orientation I M (Fin (2 * n))) (hJ : J.IsIntegrable) (hσ : σ.IsClosed)
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    {k l p q : ℕ} (hkl : k + l = 2 * n) (hpq : p + q = k) (hp : p ≤ n) (hq : q ≤ n) :
    finrank ℂ (hodgePiece J k p q) ≤ finrank ℂ (hodgePiece J l (n - q) (n - p)) := by
  have hlk : l + k = 2 * n := by omega
  have hA := SmoothAlmostComplexStructure.inner_apply_left_eq_neg hg
  let S := (LinearMap.range (J.typeProjection (F := ℂ) (k := k) p q)).comap
    (complexHarmonicForms o hkl).subtype
  have e : S ≃ₗ[ℂ] hodgePiece J k p q := by
    rw [hodgePiece_eq_map_complexHarmonicForms o hJ hσ hg hkl]
    exact Submodule.equivMapOfInjective _
      (complexHarmonicForms.toComplexDeRhamCohomology_bijective o hkl).1 S
  -- The Hodge star of a harmonic form of type `(p,q)`, as a harmonic form.
  let star : complexHarmonicForms o hkl →ₗ[ℂ] complexHarmonicForms o hlk :=
    (SmoothForm.complexHodgeStar o hkl).restrict fun φ hφ ↦
      (complexHodgeStar_mem_complexHarmonicForms_iff o hkl hlk φ).2 hφ
  let f : S →ₗ[ℂ] hodgePiece J l (n - q) (n - p) :=
    ((complexHarmonicForms.toComplexDeRhamCohomology o hlk ∘ₗ star) ∘ₗ S.subtype).codRestrict
      _ fun φ ↦ by
        rw [hodgePiece_eq_map_complexHarmonicForms o hJ hσ hg hlk]
        refine ⟨star φ, ?_, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, J.mem_range_typeProjection_iff (by omega)]
        have hφ := φ.property
        rw [Submodule.mem_comap, J.mem_range_typeProjection_iff hpq] at hφ
        exact hφ.complexHodgeStar o hkl hA hp hq
  have hf : Function.Injective f := by
    intro φ ψ h
    have h' := (complexHarmonicForms.toComplexDeRhamCohomology_bijective o hlk).1
      (congrArg Subtype.val h)
    exact Subtype.ext <| Subtype.ext <|
      SmoothForm.complexHodgeStar_injective o hkl (congrArg Subtype.val h')
  rw [← e.finrank_eq]
  exact LinearMap.finrank_le_finrank_of_injective hf

/-- **Serre symmetry of the Hodge numbers**: on a compact Hausdorff boundaryless manifold modelled
on a space of dimension `2 n`, with `J` integrable and `σ` a closed two-form compatible with `J`,
`h^{p,q} = h^{n-q,n-p}` for `p ≤ n` and `q ≤ n`: the space `H^{p,q}` of `H^k_dR(M; ℂ)` and the space
`H^{n-q,n-p}` of `H^{2n-k}_dR(M; ℂ)` have the same dimension. -/
theorem finrank_hodgePiece_serre (hσ : σ.IsClosed) (hc : σ.Compatible J) (hJ : J.IsIntegrable)
    (hn : finrank ℝ E = 2 * n) {k p q : ℕ} (hpq : p + q = k) (hp : p ≤ n) (hq : q ≤ n) :
    finrank ℂ (hodgePiece J k p q) =
      finrank ℂ (hodgePiece J (2 * n - k) (n - q) (n - p)) := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨hc.metric.toRiemannianMetric⟩
  have hg := hc.inner_eq_eval₂
  have o := hc.isNondegenerate.volumeOrientation hn
  refine le_antisymm (finrank_hodgePiece_le o hJ hσ hg (by omega) hpq hp hq) ?_
  have h := finrank_hodgePiece_le o hJ hσ hg (k := 2 * n - k) (l := k) (by omega) (by omega)
    (Nat.sub_le n q) (Nat.sub_le n p)
  rwa [Nat.sub_sub_self hp, Nat.sub_sub_self hq] at h

end complexDeRhamCohomology

variable {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M} {n : ℕ}

open complexDeRhamCohomology in
/-- **The Betti numbers are sums of Hodge numbers**: on a compact Hausdorff boundaryless manifold,
with `J` integrable and `σ` a closed two-form compatible with `J`, the `k`-th Betti number is
`b_k = ∑_{p+q=k} h^{p,q}`. -/
theorem finrank_deRhamCohomology_eq_sum (hσ : σ.IsClosed) (hc : σ.Compatible J)
    (hJ : J.IsIntegrable) (k : ℕ) :
    finrank ℝ (deRhamCohomology I M k) =
      ∑ p ∈ Finset.range (k + 1), finrank ℂ (hodgePiece J k p (k - p)) := by
  have hH := isHodgeDecomposition_hodgePiece_of_compatible hσ hc hJ k
  have hfin : {p : ℤ | hodgePiece J k p.toNat (k - p).toNat ≠ ⊥} ⊆
      ↑((Finset.range (k + 1)).map Nat.castEmbedding : Finset ℤ) := fun p hp ↦ by
    by_contra h
    refine hp (hodgePiece_toNat_eq_bot J ?_)
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_range,
      Nat.castEmbedding_apply, not_exists, not_and] at h
    by_contra h'
    exact h p.toNat (by omega) (by omega)
  rw [← finrank_complexDeRhamCohomology,
    ← (Hodge.HodgeStructureOn.ofDecomposition hH).finsum_hodgeNumber_eq_finrank,
    finsum_eq_sum_of_support_subset _ fun p hp ↦ hfin fun h ↦ hp (by
      rw [Hodge.HodgeStructureOn.hodgeNumber_def, Hodge.HodgeStructureOn.ofDecomposition_piece, h,
        finrank_bot]),
    Finset.sum_map]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [Hodge.HodgeStructureOn.hodgeNumber_def, Hodge.HodgeStructureOn.ofDecomposition_piece,
    Nat.castEmbedding_apply, Int.toNat_natCast, Int.toNat_sub', Int.toNat_natCast]

open complexDeRhamCohomology in
/-- **The odd Betti numbers of a compact Kähler manifold are even**: on a compact Hausdorff
boundaryless manifold, with `J` integrable and `σ` a closed two-form compatible with `J`, the
`k`-th Betti number is even for odd `k`. -/
theorem even_finrank_deRhamCohomology_of_odd (hσ : σ.IsClosed) (hc : σ.Compatible J)
    (hJ : J.IsIntegrable) {k : ℕ} (hk : Odd k) :
    Even (finrank ℝ (deRhamCohomology I M k)) := by
  obtain ⟨j, rfl⟩ := hk
  set f : ℕ → ℕ := fun p ↦ finrank ℂ (hodgePiece J (2 * j + 1) p (2 * j + 1 - p))
  -- The terms of index `j + 1 + p` and `j - p` agree by Hodge symmetry.
  have hf : ∀ p ∈ Finset.range (j + 1), f (j + 1 + p) = f (j + 1 - 1 - p) := fun p hp ↦ by
    rw [Finset.mem_range] at hp
    simp only [f]
    rw [finrank_hodgePiece_symm]
    rw [show 2 * j + 1 - (j + 1 + p) = j + 1 - 1 - p by omega,
      show 2 * j + 1 - (j + 1 - 1 - p) = j + 1 + p by omega]
  rw [finrank_deRhamCohomology_eq_sum hσ hc hJ, show 2 * j + 1 + 1 = (j + 1) + (j + 1) by ring,
    Finset.sum_range_add, Finset.sum_congr rfl hf, Finset.sum_range_reflect]
  exact ⟨_, rfl⟩

/-- **The Hodge decomposition on a closed Kähler manifold**: let `M` be a compact Hausdorff
boundaryless manifold modelled on a space of dimension `2 n`, with a Kähler form `σ` for an
integrable almost complex structure `J`. In every degree `k`,
* the subspaces `H^{p,q}` of `H^k_dR(M; ℂ)`, `p + q = k`, of classes of closed forms of type
  `(p,q)`, form a Hodge decomposition of weight `k` for complex conjugation: an internal direct
  sum, with `H^{q,p}` the conjugate of `H^{p,q}`;
* the de Rham cohomology `H^k_dR(M; ℝ)` is finite-dimensional;
* the Hodge numbers `h^{p,q} = dim H^{p,q}` satisfy `h^{p,q} = h^{q,p}` and, for `p, q ≤ n`,
  `h^{p,q} = h^{n-q,n-p}`;
* the Betti number `b_k = dim H^k_dR(M; ℝ)` is `∑_{p+q=k} h^{p,q}`, and it is even for odd `k`.

Milestone: *Hodge decomposition on closed Kähler manifolds*. -/
theorem SmoothTwoForm.IsKahler.hodge_decomposition
    (hK : σ.IsKahler J) (hJ : J.IsIntegrable) (hn : finrank ℝ E = 2 * n) (k : ℕ) :
    Hodge.IsHodgeDecomposition (complexDeRhamCohomology.conj k) k
        (fun p : ℤ ↦ complexDeRhamCohomology.hodgePiece J k p.toNat (k - p).toNat) ∧
      FiniteDimensional ℝ (deRhamCohomology I M k) ∧
      (∀ p q, p + q = k →
        finrank ℂ (complexDeRhamCohomology.hodgePiece J k p q) =
          finrank ℂ (complexDeRhamCohomology.hodgePiece J k q p)) ∧
      (∀ p q, p + q = k → p ≤ n → q ≤ n →
        finrank ℂ (complexDeRhamCohomology.hodgePiece J k p q) =
          finrank ℂ (complexDeRhamCohomology.hodgePiece J (2 * n - k) (n - q) (n - p))) ∧
      finrank ℝ (deRhamCohomology I M k) =
        ∑ p ∈ Finset.range (k + 1),
          finrank ℂ (complexDeRhamCohomology.hodgePiece J k p (k - p)) ∧
      (Odd k → Even (finrank ℝ (deRhamCohomology I M k))) :=
  ⟨complexDeRhamCohomology.isHodgeDecomposition_hodgePiece_of_compatible hK.isClosed
      hK.compatible hJ k,
    inferInstance,
    fun p q _ ↦ complexDeRhamCohomology.finrank_hodgePiece_symm J k p q,
    fun _ _ hpq hp hq ↦ complexDeRhamCohomology.finrank_hodgePiece_serre hK.isClosed
      hK.compatible hJ hn hpq hp hq,
    finrank_deRhamCohomology_eq_sum hK.isClosed hK.compatible hJ k,
    even_finrank_deRhamCohomology_of_odd hK.isClosed hK.compatible hJ⟩

end TauCeti

end

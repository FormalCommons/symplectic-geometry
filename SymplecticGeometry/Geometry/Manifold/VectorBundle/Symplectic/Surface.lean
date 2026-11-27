/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Basic
import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Orthogonal
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Section.Nonvanishing
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.ComplexStructure.Basic
import SymplecticGeometry.LinearAlgebra.Symplectic.Darboux

/-!
# Symplectic frames over surfaces with boundary

Let `ω` be a smooth nondegenerate two-form on a smooth real vector bundle `V` over a compact
connected surface `S` whose boundary is not empty. This file shows that `ω` has a global smooth
symplectic frame, modelled on the standard symplectic space `StdSpace κ`. No orientation of `S`
is used.

## Main results

* `ContMDiffTwoForm.IsNondegenerate.exists_darboux_contMDiffSection_of_boundary_nonempty_of_le`:
  over a compact connected manifold of dimension `n + 2` whose boundary is not empty, a
  nondegenerate smooth two-form on a bundle of rank `2 (k + r)`, with `n + 2 ≤ 2 (r + 1)`, has
  `k` pairs of smooth sections that satisfy the Darboux relations at every point.
* `ContMDiffTwoForm.IsNondegenerate.exists_isSymplecticFrameOn_univ_of_boundary_nonempty`: over a
  compact connected surface whose boundary is not empty, a nondegenerate smooth two-form on a
  bundle of rank `2 |κ|` has a global smooth symplectic frame for `stdForm κ`. The frame comes
  from the Darboux sections through `ContMDiffTwoForm.exists_isSymplecticFrameOn_of_darboux`.

## Implementation notes

The sections are built one pair at a time, by a symplectic version of the induction of
`Bundle.ContMDiffRiemannianMetric.exists_orthonormal_contMDiffSection_of_boundary_nonempty_of_le`
(`Hermitian/Surface.lean`), itself adapted from Tau Ceti's
`Bundle.ContMDiffRiemannianMetric.exists_orthonormal_contMDiffSection_of_finrank_lt`. Once `j`
pairs `aᵢ`, `bᵢ` are chosen, their span `D` is a smooth subbundle on which `ω` is nondegenerate,
so its `ω`-orthogonal is a smooth subbundle of rank `2 (k + r - j)`
(`TauCeti.HasLocalContMDiffSubbundleFrames.orthogonal`), at least `n + 2`. It has a smooth
nowhere-zero section `u`
(`SymplecticGeometry.exists_contMDiffSection_forall_ne_zero_of_boundary_nonempty`). For a complex
structure `J` compatible with `ω` (`ContMDiffTwoForm.IsNondegenerate.exists_compatible`),
`c = ω(u, J u)` is positive, and the projection of `c⁻¹ J u` to the `ω`-orthogonal of `D` along
`D`, `v ↦ v - ∑ᵢ (ω(v, bᵢ) aᵢ - ω(v, aᵢ) bᵢ)`, completes `u` to a new pair. No complex vector
bundle is needed.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 2.1.3 and Proposition 2.6.7
* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  proof of Theorem C.1.10
-/

public noncomputable section

open _root_.Bundle Module Set
open scoped Manifold

namespace SymplecticGeometry

open StdSpace


namespace Bundle.ContMDiffTwoForm

section Step

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace M] [ChartedSpace HB M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] {n : ℕ∞} {ω : ContMDiffTwoForm I n F V}

/-! ### One step of the induction -/

variable [ContMDiffVectorBundle n F V I]

/-- The `ω`-orthogonal of the span of `k` pairs of `Cⁿ` sections `aᵢ`, `bᵢ` that satisfy the
Darboux relations everywhere is a `Cⁿ` subbundle of rank `rank V - 2k`. -/
private theorem hasLocalContMDiffSubbundleFrames_orthogonal_span_darboux {k : ℕ}
    {a b : Fin k → ∀ x, V x} (ha : ∀ i, CMDiff n (T% (a i))) (hb : ∀ i, CMDiff n (T% (b i)))
    (haa : ∀ x i j, ω.bilinFormAt x (a i x) (a j x) = 0)
    (hbb : ∀ x i j, ω.bilinFormAt x (b i x) (b j x) = 0)
    (hab : ∀ x i j, ω.bilinFormAt x (a i x) (b j x) = if i = j then 1 else 0) :
    TauCeti.HasLocalContMDiffSubbundleFrames I n F (Fin (finrank ℝ F - (k + k))) fun x ↦
      (ω.bilinFormAt x).orthogonal (Submodule.span ℝ (range (Fin.append a b · x))) := by
  classical
  have hflat (x : M) : (ω.flat x).toLinearMap₁₂ = ω.bilinFormAt x := by
    rw [← ω.toBilinForm_flat x, ContinuousLinearMap.toBilinForm]
  -- The span `D` of the pairs, with its global frame `X`.
  let X : Fin (k + k) → ∀ x, V x := Fin.append a b
  let D (x : M) : Submodule ℝ (V x) := Submodule.span ℝ (range (X · x))
  have hXa (i : Fin k) : X (Fin.castAdd k i) = a i := Fin.append_left a b i
  have hXb (i : Fin k) : X (Fin.natAdd k i) = b i := Fin.append_right a b i
  have haD (x : M) (i : Fin k) : a i x ∈ D x :=
    Submodule.subset_span ⟨Fin.castAdd k i, congrFun (hXa i) x⟩
  have hbD (x : M) (i : Fin k) : b i x ∈ D x :=
    Submodule.subset_span ⟨Fin.natAdd k i, congrFun (hXb i) x⟩
  -- A combination of the `X p x` that is `ω`-orthogonal to all `aᵢ`, `bᵢ` has zero coefficients.
  have hzero (x : M) (g : Fin (k + k) → ℝ)
      (hg : ∀ j, ω.bilinFormAt x (∑ p, g p • X p x) (b j x) = 0 ∧
        ω.bilinFormAt x (∑ p, g p • X p x) (a j x) = 0) (p : Fin (k + k)) : g p = 0 := by
    have hsum : ∑ p, g p • X p x =
        ∑ i, ((g ∘ Fin.castAdd k) i • a i x + (g ∘ Fin.natAdd k) i • b i x) := by
      rw [Fin.sum_univ_add, ← Finset.sum_add_distrib]
      simp only [hXa, hXb, Function.comp_apply]
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) p
    · rw [← Function.comp_apply (f := g), ← (ω.bilinFormAt x).apply_sum_smul_add_smul_eq_left_coeff
        (hbb x) (hab x) (g ∘ Fin.castAdd k) (g ∘ Fin.natAdd k) j, ← hsum]
      exact (hg j).1
    · rw [← Function.comp_apply (f := g), ← neg_eq_zero,
        ← (ω.isAlt_bilinFormAt x).apply_sum_smul_add_smul_eq_neg_right_coeff (haa x) (hab x)
          (g ∘ Fin.castAdd k) _ j, ← hsum]
      exact (hg j).2
  have hX (p : Fin (k + k)) : CMDiff n (T% (X p)) := by
    refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) p
    · rw [hXa]
      exact ha i
    · rw [hXb]
      exact hb i
  have hD : TauCeti.HasLocalContMDiffSubbundleFrames I n F (Fin (k + k)) D :=
    TauCeti.hasLocalContMDiffSubbundleFrames_iff.2 fun x ↦ ⟨univ, isOpen_univ, mem_univ x, X,
      ⟨fun p ↦ (hX p).continuous.continuousOn, fun {y} _ ↦ Fintype.linearIndependent_iff.2
        fun g hg ↦ hzero y g fun j ↦ by simp [hg], fun _ ↦ rfl⟩, fun p ↦ (hX p).contMDiffOn⟩
  -- `D` meets its `ω`-orthogonal only in `0`, so `ω` is nondegenerate on `D`.
  have hdisj (x : M) : Disjoint (D x) ((ω.bilinFormAt x).orthogonal (D x)) := by
    refine Submodule.disjoint_def.2 fun s hs hs' ↦ ?_
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hs
    have hrefl := (ω.isAlt_bilinFormAt x).isRefl
    have h := LinearMap.BilinForm.mem_orthogonal_iff.1 hs'
    simp [hzero x g fun j ↦ ⟨hrefl _ _ (h _ (hbD x j)), hrefl _ _ (h _ (haD x j))⟩]
  simp only [← orthogonal_flat]
  refine hD.orthogonal ω.contMDiff_flat (fun x ↦ ?_) fun x ↦ ?_
  · rw [hflat]
    exact (ω.isAlt_bilinFormAt x).isRefl
  · rw [hflat]
    exact (ω.bilinFormAt x).nondegenerate_restrict_of_disjoint_orthogonal
      (ω.isAlt_bilinFormAt x).isRefl (hdisj x)

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle n F V I] in
/-- Let `aᵢ`, `bᵢ` be `Cⁿ` sections that satisfy the Darboux relations everywhere, `u` a
nowhere-zero `Cⁿ` section `ω`-orthogonal to all of them, and `J` a complex structure tamed by
`ω`. Then the projection `v` of `ω(u, J u)⁻¹ J u` along the span of the `aᵢ`, `bᵢ` is a `Cⁿ`
section `ω`-orthogonal to all `aᵢ`, `bᵢ`, with `ω(u, v) = 1`. -/
private theorem exists_darboux_completion {J : ContMDiffComplexStructure I n F V}
    (hJ : ω.Tames J) {k : ℕ} {a b : Fin k → ∀ x, V x} (ha : ∀ i, CMDiff n (T% (a i)))
    (hb : ∀ i, CMDiff n (T% (b i))) (haa : ∀ x i j, ω.bilinFormAt x (a i x) (a j x) = 0)
    (hbb : ∀ x i j, ω.bilinFormAt x (b i x) (b j x) = 0)
    (hab : ∀ x i j, ω.bilinFormAt x (a i x) (b j x) = if i = j then 1 else 0)
    {u : ∀ x, V x} (hu : CMDiff n (T% u)) (hu₀ : ∀ x, u x ≠ 0)
    (hau : ∀ x i, ω.bilinFormAt x (a i x) (u x) = 0)
    (hbu : ∀ x i, ω.bilinFormAt x (b i x) (u x) = 0) :
    ∃ v : ∀ x, V x, CMDiff n (T% v) ∧ (∀ x j, ω.bilinFormAt x (v x) (a j x) = 0) ∧
      (∀ x j, ω.bilinFormAt x (v x) (b j x) = 0) ∧ ∀ x, ω.bilinFormAt x (u x) (v x) = 1 := by
  set y : ∀ x, V x := fun x ↦ J x (u x)
  have hy : CMDiff n (T% y) := J.toEndomorphism.contMDiff.clm_bundle_apply hu
  set c : M → ℝ := fun x ↦ ω.bilinFormAt x (u x) (y x)
  have hc₀ (x : M) : 0 < c x := tames_def.1 hJ x (u x) (hu₀ x)
  refine ⟨fun x ↦ (c x)⁻¹ • (y x - ∑ i,
    (ω.bilinFormAt x (y x) (b i x) • a i x + -ω.bilinFormAt x (y x) (a i x) • b i x)),
    ((ω.contMDiff_bilinFormAt hu hy).inv₀ fun x ↦ (hc₀ x).ne').smul_section (hy.sub_section
      (ContMDiff.sum_section fun i _ ↦
        ((ω.contMDiff_bilinFormAt hy (hb i)).smul_section (ha i)).add_section
          ((ω.contMDiff_bilinFormAt hy (ha i)).neg.smul_section (hb i)))),
    fun x j ↦ ?_, fun x j ↦ ?_, fun x ↦ ?_⟩
  · rw [map_smul, LinearMap.smul_apply,
      (ω.isAlt_bilinFormAt x).apply_sub_sum_apply_smul_add_smul_fst_eq_zero (haa x) (hab x),
      smul_zero]
  · rw [map_smul, LinearMap.smul_apply,
      (ω.bilinFormAt x).apply_sub_sum_apply_smul_add_smul_snd_eq_zero (hbb x) (hab x), smul_zero]
  have hua (i : Fin k) : ω.bilinFormAt x (u x) (a i x) = 0 :=
    (ω.isAlt_bilinFormAt x).eq_iff.1 (hau x i)
  have hub (i : Fin k) : ω.bilinFormAt x (u x) (b i x) = 0 :=
    (ω.isAlt_bilinFormAt x).eq_iff.1 (hbu x i)
  simp only [map_smul, map_sub, map_sum, map_add, hua, hub, smul_eq_mul, mul_zero, add_zero,
    Finset.sum_const_zero, sub_zero]
  exact inv_mul_cancel₀ (hc₀ x).ne'

end Step

section Boundary

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 2)) M]
  [IsManifold (𝓡∂ (n + 2)) ((⊤ : ℕ∞) : WithTop ℕ∞) M] [CompactSpace M] [ConnectedSpace M]
  [T2Space M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ((⊤ : ℕ∞) : WithTop ℕ∞) F V (𝓡∂ (n + 2))]
  {ω : ContMDiffTwoForm (𝓡∂ (n + 2)) ⊤ F V}

/-- **Darboux sections over manifolds with boundary.** Let `ω` be a nondegenerate smooth
two-form on a smooth real vector bundle of rank `2 (k + r)` over a compact connected manifold of
dimension `n + 2 ≤ 2 (r + 1)` whose boundary is not empty. Then there are `k` pairs of smooth
sections `aᵢ`, `bᵢ` that satisfy the Darboux relations `ω(aᵢ, aⱼ) = 0`, `ω(bᵢ, bⱼ) = 0` and
`ω(aᵢ, bⱼ) = δᵢⱼ` at every point. -/
theorem IsNondegenerate.exists_darboux_contMDiffSection_of_boundary_nonempty_of_le
    (hω : ω.IsNondegenerate) (hM : ((𝓡∂ (n + 2)).boundary M).Nonempty) {k r : ℕ}
    (hk : finrank ℝ F = 2 * (k + r)) (hdim : n + 2 ≤ 2 * (r + 1)) :
    ∃ a b : Fin k → ∀ x, V x, (∀ i, CMDiff ((⊤ : ℕ∞) : WithTop ℕ∞) (T% (a i))) ∧
      (∀ i, CMDiff ((⊤ : ℕ∞) : WithTop ℕ∞) (T% (b i))) ∧
      (∀ x i j, ω.bilinFormAt x (a i x) (a j x) = 0) ∧
      (∀ x i j, ω.bilinFormAt x (b i x) (b j x) = 0) ∧
      ∀ x i j, ω.bilinFormAt x (a i x) (b j x) = if i = j then 1 else 0 := by
  induction k generalizing r with
  | zero => exact ⟨fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0,
      fun _ i ↦ i.elim0, fun _ i ↦ i.elim0, fun _ i ↦ i.elim0⟩
  | succ k ih =>
    classical
    obtain ⟨a, b, ha, hb, haa, hbb, hab⟩ := ih (r := r + 1) (by rw [hk]; ring) (by omega)
    have hskew (x : M) (u v : V x) : ω.bilinFormAt x u v = -ω.bilinFormAt x v u :=
      (LinearMap.IsAlt.neg (ω.isAlt_bilinFormAt x) v u).symm
    have hself (x : M) (u : V x) : ω.bilinFormAt x u u = 0 :=
      (ω.isAlt_bilinFormAt x).self_eq_zero u
    -- The `ω`-orthogonal `W` of the pairs chosen so far is a smooth subbundle of rank at least
    -- `n + 2`, so it has a nowhere-zero smooth section `u`.
    have hW := hasLocalContMDiffSubbundleFrames_orthogonal_span_darboux ha hb haa hbb hab
    let W (x : M) := (ω.bilinFormAt x).orthogonal (Submodule.span ℝ (range (Fin.append a b · x)))
    let := TauCeti.subbundleTopology F (F' := Fin (finrank ℝ F - (k + k)) → ℝ) W
    let := hW.fiberBundle
    let := hW.vectorBundle
    let := hW.contMDiffVectorBundle
    have hr : n + 2 ≤ finrank ℝ (Fin (finrank ℝ F - (k + k)) → ℝ) := by
      simp only [finrank_fin_fun]
      omega
    obtain ⟨t, ht⟩ := exists_contMDiffSection_forall_ne_zero_of_boundary_nonempty
      (V := fun x ↦ W x) (F := Fin (finrank ℝ F - (k + k)) → ℝ) hM hr
    set u : ∀ x, V x := fun x ↦ (t x : V x)
    have hu : CMDiff ((⊤ : ℕ∞) : WithTop ℕ∞) (T% u) :=
      hW.contMDiff_totalSpace_inclusion.comp t.contMDiff
    have hXu (x : M) (p : Fin (k + k)) : ω.bilinFormAt x (Fin.append a b p x) (u x) = 0 :=
      LinearMap.BilinForm.mem_orthogonal_iff.1 (t x).property _ (Submodule.subset_span ⟨p, rfl⟩)
    have hau (x : M) (i : Fin k) : ω.bilinFormAt x (a i x) (u x) = 0 := by
      simpa only [Fin.append_left] using hXu x (Fin.castAdd k i)
    have hbu (x : M) (i : Fin k) : ω.bilinFormAt x (b i x) (u x) = 0 := by
      simpa only [Fin.append_right] using hXu x (Fin.natAdd k i)
    -- Complete `u` to a pair through a compatible complex structure.
    obtain ⟨J, hJ⟩ := hω.exists_compatible
    obtain ⟨v, hv, hva, hvb, huv⟩ := exists_darboux_completion hJ.tames ha hb haa hbb hab hu
      (fun x ↦ by simpa [u] using ht x) hau hbu
    refine ⟨Fin.cons u a, Fin.cons v b, fun i ↦ ?_, fun i ↦ ?_, fun x i j ↦ ?_, fun x i j ↦ ?_,
      fun x i j ↦ ?_⟩
    · exact Fin.cases (by simpa using hu) (fun i ↦ by simpa using ha i) i
    · exact Fin.cases (by simpa using hv) (fun i ↦ by simpa using hb i) i
    · cases i using Fin.cases <;> cases j using Fin.cases <;>
        simp [hself, haa, hau, hskew x (u x) (a _ x)]
    · cases i using Fin.cases <;> cases j using Fin.cases <;>
        simp [hself, hbb, hvb, hskew x (b _ x) (v x)]
    · cases i using Fin.cases <;> cases j using Fin.cases <;>
        simp [huv, hab, hva, hskew x (a _ x) (v x), hbu, hskew x (u x) (b _ x),
          Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

end Boundary

section Surface

variable {S : Type*} [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) ((⊤ : ℕ∞) : WithTop ℕ∞) S] [CompactSpace S] [ConnectedSpace S] [T2Space S]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : S → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ((⊤ : ℕ∞) : WithTop ℕ∞) F V (𝓡∂ 2)]
  {ω : ContMDiffTwoForm (𝓡∂ 2) ⊤ F V}

/-- **Symplectic frames over surfaces with boundary.** Let `ω` be a nondegenerate smooth
two-form on a smooth real vector bundle `V` of rank `2 |κ|` over a compact connected surface `S`
whose boundary is not empty. Then `ω` has a global smooth symplectic frame for the standard form
`stdForm κ`: smooth linear isomorphisms `Φ x : StdSpace κ ≃L[ℝ] V x` with
`ω(Φ x v, Φ x w) = stdForm κ v w`. -/
theorem IsNondegenerate.exists_isSymplecticFrameOn_univ_of_boundary_nonempty
    (hω : ω.IsNondegenerate) (hS : ((𝓡∂ 2).boundary S).Nonempty) {κ : Type*} [Fintype κ]
    (hκ : finrank ℝ F = 2 * Fintype.card κ) :
    ∃ Φ : ∀ x, StdSpace κ ≃L[ℝ] V x, ω.IsSymplecticFrameOn (stdForm κ) univ Φ := by
  classical
  obtain ⟨a, b, ha, hb, haa, hbb, hab⟩ :=
    hω.exists_darboux_contMDiffSection_of_boundary_nonempty_of_le (n := 0) hS (r := 0)
      (by rw [hκ, add_zero]) le_rfl
  -- Index the pairs by `κ`.
  let e := Fintype.equivFin κ
  obtain ⟨Φ, hΦ, -⟩ := exists_isSymplecticFrameOn_of_darboux hκ (U := univ)
    (a := fun i ↦ a (e i)) (b := fun i ↦ b (e i)) (fun i ↦ (ha (e i)).contMDiffOn)
    (fun i ↦ (hb (e i)).contMDiffOn) (fun x _ i j ↦ haa x (e i) (e j))
    (fun x _ i j ↦ hbb x (e i) (e j)) (fun x _ i j ↦ by simp only [hab, e.injective.eq_iff])
  exact ⟨Φ, hΦ⟩

end Surface

end Bundle.ContMDiffTwoForm

end SymplecticGeometry

end

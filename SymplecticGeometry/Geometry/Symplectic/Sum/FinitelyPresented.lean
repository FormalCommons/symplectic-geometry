/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import SymplecticGeometry.Geometry.Manifold.ModelTransport.Boundaryless
public import SymplecticGeometry.Geometry.Manifold.ModelTransport.Remodel
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Diffeomorph
public import SymplecticGeometry.Geometry.Symplectic.Sum.GraphTorus
public import SymplecticGeometry.Topology.Homotopy.AddCircle
public import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
public import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.AddCircle
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.BasepointChange
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.Prod.Basic
import SymplecticGeometry.Geometry.Manifold.GeneralPosition
import SymplecticGeometry.Geometry.Manifold.Instances.Surface.FundamentalGroup
import SymplecticGeometry.Geometry.Manifold.Instances.Surface.Orientation
import SymplecticGeometry.Geometry.Manifold.NullSet
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.SmoothEmbedding
import SymplecticGeometry.Geometry.Symplectic.Sum.FundamentalGroup
import SymplecticGeometry.GroupTheory.FinitelyPresentedGroup
import SymplecticGeometry.GroupTheory.Subgroup.NormalClosure
import SymplecticGeometry.GroupTheory.SurfaceGroup.Quotient
import SymplecticGeometry.LinearAlgebra.Complex.Finrank

/-!
# The realization of finitely presented groups

This file shows that a group with a finite presentation is, up to isomorphism, `π₁` of some
compact, connected symplectic four-manifold without boundary
(`exists_fundamentalGroup_mulEquiv`), by Gompf's construction: sum the product of a closed
surface with the torus `T²` with copies of the rational elliptic surface along disjoint
symplectic tori. Most of the file builds those tori and computes the effect of the sums on `π₁`.

Let `Σ` be a Hausdorff manifold of dimension at least two, smooth and
without boundary, such as the closed surface of genus `g`
(`SymplecticGeometry.ClosedSurface g`), and let `T = ∀ j : ι ⊕ ι, AddCircle (p j)` be the
standard torus with one of its coordinates `i`. For finitely many based loops `γ k` at `x` in `Σ`,
`exists_graphTorus_family` gives smooth circle maps `h k : AddCircle (p i) → Σ` and a point `z`
of `Σ` such that

* each `h k` is freely homotopic to the circle map `(γ k).toAddCircle` of `γ k`;
* the loops of the `h k`, brought to `x` along any paths, normally generate the same subgroup of
  `π₁(Σ, x)` as the `γ k`;
* the graph tori `y ↦ (h k (y i), y)` (`SymplecticGeometry.graphTorus`) are pairwise disjoint;
* each of them is disjoint from the fibre torus `{z} × T`, which is the graph torus of the
  constant map at `z`.

The maps come from the general position of finitely many circle maps
(`SymplecticGeometry.exists_contMDiff_homotopic_forall_ne_addCircle`), applied to the circle maps
`(γ k).toAddCircle` of the loops, and `z` from the density of the complement of finitely many
smooth loops (`SymplecticGeometry.dense_compl_iUnion_range_addCircle`). Free homotopies do not
change the normal closure
(`ContinuousMap.normalClosure_range_toLoop_eq_of_homotopic_toAddCircle`).

When `Σ` is a surface with a nondegenerate two-form `σ`, such as an area form of the closed
surface (`SymplecticGeometry.ClosedSurface.exists_isSymplectic`), the rest is in
`Sum/GraphTorus.lean`, for every graph torus and so for the fibre torus too: it pulls the product
form `pr₁^* σ + pr₂^* ω_T` back to `ω_T = TauCeti.torusSymplecticForm p`
(`SymplecticGeometry.mpullback_graphTorus_prod_torusSymplecticForm`), so it is symplectic
(`SymplecticGeometry.hasSymplecticTangentImages_graphTorus`); it has a symplectic framing
(`SymplecticGeometry.nonempty_symplecticFraming_graphTorus`); and in
`π₁(Σ × T) ≃* π₁(Σ) × π₁(T)` it sends the generator of the `i`-th circle of `T` to the pair of
the loop of `h k` and that generator, and every other generator `α` to `(1, α)`
(`SymplecticGeometry.prodMulEquiv_mapOfEq_graphTorus_torusLoop_single_self`,
`SymplecticGeometry.prodMulEquiv_mapOfEq_graphTorus_torusLoop_single_of_ne`).

Summing `Σ × T` with a copy of the rational elliptic surface along each of these tori kills, in
the fundamental group, the image of `π₁(T)` under each torus. Before any sum, the effect of killing
these images is computed here: with `h` and `z` as `exists_graphTorus_family` gives them, the
quotient of `π₁(Σ × T, (x, y))` by the normal closure of the images of `π₁(T, 0)` under the graph
tori of the `h k` and the fibre torus `{z} × T`, each brought to `(x, y)` along a path, is
`π₁(Σ, x)` modulo the normal closure of the `γ k`. Under `π₁(Σ × T) ≃* π₁(Σ) × π₁(T)`, the fibre
torus gives all of `1 × π₁(T)`; this is the kernel of the first projection, so the quotient is a
quotient of `π₁(Σ, x)` (`Subgroup.map_normalClosure`, `Subgroup.comap_map_eq_self`,
`QuotientGroup.liftEquiv`). The first projection of the image of the graph torus of `h k` is
generated by the loop of `h k` brought to `x`, and contains that loop, the image of the loop around
the `i`-th circle of `T`
(`SymplecticGeometry.map_fst_fundamentalGroupMulEquivOfPath_map_graphTorus_mem_zpowers`,
`SymplecticGeometry.map_fst_fundamentalGroupMulEquivOfPath_map_graphTorus_torusLoop_single_self`,
in `Sum/GraphTorus.lean`).

To sum `Σ × T` with the rational elliptic surface, both must be charted on one model, and
`rationalEllipticSurface.OnModel e` is charted on a real normed space `V`. So `Σ × T`, modelled on
the product of the model `I` of `Σ` and of the model of the torus, is moved to the model
`𝓘(ℝ, V)`: first to the model vector space of that product model (Tau Ceti's
`TauCeti.BoundarylessModel`), then along a real linear isomorphism
`L : E × (ι ⊕ ι → ℝ) ≃L[ℝ] V` (`SymplecticGeometry.Remodel`); for the closed surface and `T = T²`,
`V = Fin 2 → ℂ` is one choice. The product form, the graph tori, their framings and
their disjointness all move along the identity of the points
(`SymplecticGeometry.ProdTorusOnModel.diffeomorph`), and the copy keeps the compactness,
connectedness and separation of `Σ × T`.

The milestone assembles these pieces. Write `G` as the group presented by `g` letters and words
`w j` (`Group.IsFinitelyPresented.exists_one_le_mulEquiv_presentedGroup`). Through
`ClosedSurface.fundamentalGroupMulEquiv g`, choose loops on the closed surface `F` of genus `g`
for the generators `b k` of the surface group and for the words `w j` read in its generators
`a k`; modulo their normal closure, `π₁(F)` is `G`
(`TauCeti.SurfaceGroup.Orientable.quotientEquivPresentedGroup`). Their graph tori and a fibre
torus, moved to the model `EuclideanSpace ℝ (Fin 4)`, are disjoint framed symplectic tori in
`F × T²`. Summing with a copy of the rational elliptic surface along each of them
(`exists_fundamentalGroup_mulEquiv_quotient_tori`, in `Sum/FundamentalGroup.lean`) gives
`π₁(F × T²)` modulo the normal closure of their images, which `graphTorusQuotientMulEquiv`
identifies with `G`.
The normal closures in `F × T²` and in its copy on the model correspond
(`FundamentalGroup.normalClosure_basepointChangeSubgroup_range_eq_of_eq_comp`,
`Subgroup.normalClosure_iUnion_congr`).

## Main definitions

* `SymplecticGeometry.ProdTorusOnModel I M p L`: the product `M × T`, charted on `V`.
* `SymplecticGeometry.ProdTorusOnModel.prodForm`: the product form `pr₁^* σ + pr₂^* ω_T` on it,
  nondegenerate for a nondegenerate `σ` and symplectic for a symplectic `σ`
  (`SymplecticGeometry.ProdTorusOnModel.isNondegenerate_prodForm`,
  `SymplecticGeometry.ProdTorusOnModel.isSymplectic_prodForm`).
* `SymplecticGeometry.ProdTorusOnModel.graphTorus`: the graph torus of a circle map in it, with
  symplectic tangent images
  (`SymplecticGeometry.ProdTorusOnModel.hasSymplecticTangentImages_graphTorus`) and, on a
  surface, a symplectic framing
  (`SymplecticGeometry.ProdTorusOnModel.nonempty_symplecticFraming_graphTorus`).

## Main results

* `SymplecticGeometry.exists_graphTorus_family`: smooth loops in general position, homotopic to
  given loops, whose graph tori are pairwise disjoint and miss a fibre torus.
* `SymplecticGeometry.comap_map_fst_normalClosure_eq_normalClosure_graphTorus`: the normal
  closure of the images of the graph tori of the loops and of the fibre torus is the preimage
  under the first projection of the normal closure of the loops.
* `SymplecticGeometry.graphTorusQuotientMulEquiv`: the resulting isomorphism from the quotient of
  `π₁(Σ × T, (x, y))` to `π₁(Σ, x)` modulo the normal closure of the loops.
* `SymplecticGeometry.ProdTorusOnModel.mpullback_graphTorus_prodForm`: the graph tori in
  `ProdTorusOnModel I M p L` pull its form back to `ω_T`.
* `SymplecticGeometry.ProdTorusOnModel.disjoint_range_graphTorus_iff`: they are disjoint exactly
  when the graph tori in `M × T` are.
* `SymplecticGeometry.exists_fundamentalGroup_mulEquiv`: a group with a finite presentation is
  isomorphic to `π₁` of a compact, connected, symplectic four-manifold without boundary.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Theorem 7.2.8.
* [R. E. Gompf, *A new construction of symplectic manifolds*][Gompf1995].
-/

public section

noncomputable section

open Set Function TauCeti Module
open scoped Manifold ContDiff

namespace SymplecticGeometry

section GeneralPosition

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [FiniteDimensional ℝ E] {I : ModelWithCorners ℝ E H} [I.Boundaryless] {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {ι : Type*} [Fintype ι] {p : ι ⊕ ι → ℝ} [∀ i, Fact (0 < p i)] {i : ι ⊕ ι}

/-- **Disjoint graph tori for finitely many loops.** Let `M` be a Hausdorff manifold of dimension
at least two, smooth and without boundary, and `γ k`, for `k` in a finite type, loops at `x`.
Then there are smooth circle maps `h k : AddCircle (p i) → M` and a point `z` of `M` such that

* each `h k` is freely homotopic to the circle map `(γ k).toAddCircle (p i)` of `γ k`;
* the loops `ψ k · h k · (ψ k)⁻¹` at `x`, for any paths `ψ k` from `x` to `h k 0`, normally
  generate the same subgroup of `π₁(M, x)` as the `γ k`;
* the graph tori of the `h k` in `M × T` are pairwise disjoint;
* each of them is disjoint from the fibre torus `{z} × T`, the graph torus of the constant map
  at `z`. -/
theorem exists_graphTorus_family (hE : 2 ≤ finrank ℝ E) {x : M} {κ : Type*} [Finite κ]
    (γ : κ → Path x x) :
    ∃ (h : κ → C(AddCircle (p i), M)) (hh : ∀ k, ContMDiff 𝓘(ℝ) I ∞ (h k)) (z : M),
      (∀ k, ((γ k).toAddCircle (p i)).Homotopic (h k)) ∧
      (∀ ψ : ∀ k, Path x (h k 0),
        Subgroup.normalClosure (range fun k ↦ FundamentalGroup.fromPath (.mk ((ψ k).trans
          ((h k).toLoop.trans (ψ k).symm)))) =
          Subgroup.normalClosure (range fun k ↦ FundamentalGroup.fromPath (.mk (γ k)))) ∧
      Pairwise (fun k l ↦ Disjoint (range (graphTorus (hh k))) (range (graphTorus (hh l)))) ∧
      ∀ k, Disjoint (range (graphTorus (hh k))) (range (graphTorus
        (contMDiff_const : ContMDiff 𝓘(ℝ) I ∞ fun _ : AddCircle (p i) ↦ z))) := by
  -- The circle maps of the loops, moved into general position.
  let f : κ → C(AddCircle (p i), M) := fun k ↦ (γ k).toAddCircle (p i)
  have : Nonempty M := ⟨x⟩
  obtain ⟨g, hg, hne⟩ := exists_contMDiff_homotopic_forall_ne_addCircle (I := I) hE f
  -- A point off the images of the `g k`.
  obtain ⟨z, hz⟩ := (dense_compl_iUnion_range_addCircle (I := I) (by omega)
    fun k ↦ (hg k).1.mdifferentiable (by simp)).nonempty
  simp only [mem_compl_iff, mem_iUnion, mem_range, not_exists] at hz
  exact ⟨g, fun k ↦ (hg k).1, z, fun k ↦ (hg k).2,
    ContinuousMap.normalClosure_range_toLoop_eq_of_homotopic_toAddCircle fun k ↦ (hg k).2,
    fun k l hkl ↦ (disjoint_range_graphTorus_iff _ _).2 (hne k l hkl),
    fun k ↦ (disjoint_range_graphTorus_iff _ _).2 fun t ht ↦ hz k t ht⟩

/-! ### Killing the graph tori and a fibre torus in `π₁(M × T)` -/

section FundamentalGroup

open FundamentalGroup

omit [T2Space M]

/-- Let `h k`, for `k` in a type `κ`, be smooth circle maps into `M`, and `z` a point of `M`.
In `π₁(M × T, (x, y))`, consider the images of `π₁(T, 0)` under the graph tori of the `h k`
and under the fibre torus `{z} × T`, the graph torus of the constant map at `z`, each brought to
`(x, y)` along a path. If, for every choice of paths `χ k` from `x` to `h k 0`, the loops
`χ k · h k · (χ k)⁻¹` normally generate the same subgroup of `π₁(M, x)` as loops `γ k` at `x`,
then the normal closure of these images is the preimage under the first projection of the
normal closure of the `γ k`. -/
theorem comap_map_fst_normalClosure_eq_normalClosure_graphTorus {κ : Type*} {x : M}
    {y : ∀ j, AddCircle (p j)} (γ : κ → Path x x) {h : κ → C(AddCircle (p i), M)}
    (hh : ∀ k, ContMDiff 𝓘(ℝ) I ∞ (h k))
    (hγ : ∀ χ : ∀ k, Path x (h k 0),
      Subgroup.normalClosure (range fun k ↦ fromPath (.mk ((χ k).trans
        ((h k).toLoop.trans (χ k).symm)))) =
        Subgroup.normalClosure (range fun k ↦ fromPath (.mk (γ k))))
    (z : M) (ψ : ∀ k, Path (graphTorus (hh k) 0) (x, y))
    (φ : Path (graphTorus (contMDiff_const : ContMDiff 𝓘(ℝ) I ∞ fun _ : AddCircle (p i) ↦ z) 0)
      (x, y)) :
    (Subgroup.normalClosure (range fun k ↦ fromPath (.mk (γ k)))).comap
        ((MonoidHom.fst _ _).comp (prodMulEquiv x y).toMonoidHom) =
      Subgroup.normalClosure
        ((⋃ k, (basepointChangeSubgroup (ψ k) (map (graphTorus (hh k)).toContinuousMap 0).range :
          Set (FundamentalGroup (M × ∀ j, AddCircle (p j)) (x, y)))) ∪
          basepointChangeSubgroup φ
            (map (graphTorus contMDiff_const).toContinuousMap 0).range) := by
  set S : Set (FundamentalGroup (M × ∀ j, AddCircle (p j)) (x, y)) :=
    (⋃ k, (basepointChangeSubgroup (ψ k) (map (graphTorus (hh k)).toContinuousMap 0).range :
      Set (FundamentalGroup (M × ∀ j, AddCircle (p j)) (x, y)))) ∪
      basepointChangeSubgroup φ (map (graphTorus contMDiff_const).toContinuousMap 0).range
  -- The paths from `h k 0` to `x` given by the first coordinates of the `ψ k`.
  let δ : ∀ k, Path (h k 0) x := fun k ↦
    ((ψ k).cast (graphTorus_zero (hh k)).symm rfl).map continuous_fst
  -- The first projection, as a map to `π₁(M, x)`.
  set F : FundamentalGroup (M × ∀ j, AddCircle (p j)) (x, y) →* FundamentalGroup M x :=
    (MonoidHom.fst _ _).comp (prodMulEquiv x y).toMonoidHom
  have hF (g : FundamentalGroup (M × ∀ j, AddCircle (p j)) (x, y)) : F g = map .fst (x, y) g :=
    congrArg Prod.fst (prodMulEquiv_apply x y g)
  have hFs : Function.Surjective F := Prod.fst_surjective.comp (prodMulEquiv x y).surjective
  -- The kernel of the first projection lies in the image of the fibre torus.
  have hker : F.ker ≤ Subgroup.normalClosure S := by
    intro g hg
    rw [MonoidHom.mem_ker, hF] at hg
    let e := fundamentalGroupMulEquivOfPath
      ((φ.cast (graphTorus_zero contMDiff_const).symm rfl).map continuous_snd)
    have hg' : g = fundamentalGroupMulEquivOfPath φ
        (map (graphTorus contMDiff_const).toContinuousMap 0 (e.symm (map .snd (x, y) g))) := by
      refine prod_ext ?_ ?_
      · rw [hg, map_fst_fundamentalGroupMulEquivOfPath_map_graphTorus_const]
        -- The two sides are the units of `π₁(M, x)` and of `π₁(M, (x, y).1)`, which `rw` does not
        -- identify.
        rfl
      · rw [map_snd_fundamentalGroupMulEquivOfPath_map_graphTorus]
        exact (e.apply_symm_apply _).symm
    exact Subgroup.subset_normalClosure (Or.inr ((mem_basepointChangeSubgroup _ _ _).2
      ⟨_, ⟨_, rfl⟩, hg'.symm⟩))
  have hγ' := hγ fun k ↦ (δ k).symm
  simp only [Path.symm_symm] at hγ'
  rw [← Subgroup.comap_map_eq_self hker, Subgroup.map_normalClosure _ _ hFs, ← hγ']
  refine congrArg _ (le_antisymm
    (Subgroup.normalClosure_le_normal (N := Subgroup.normalClosure _) ?_)
    (Subgroup.normalClosure_le_normal (N := Subgroup.normalClosure _) ?_))
  · -- The loop of `h k` brought to `x` comes from the loop around the `i`-th circle of the graph
    -- torus of `h k`.
    rintro _ ⟨k, rfl⟩
    classical
    exact Subgroup.subset_normalClosure ⟨_, Or.inl (mem_iUnion.2 ⟨k,
      (mem_basepointChangeSubgroup _ _ _).2 ⟨_, ⟨fromPath (.mk (torusLoop p (Pi.single i 1))), rfl⟩,
        rfl⟩⟩), (hF _).trans
          (map_fst_fundamentalGroupMulEquivOfPath_map_graphTorus_torusLoop_single_self (hh k)
            (ψ k))⟩
  · -- The graph torus of `h k` contributes the powers of the loop of `h k` brought to `x`; the
    -- fibre torus contributes nothing.
    rintro _ ⟨g, hg | hg, rfl⟩ <;> rw [hF]
    · obtain ⟨k, hg⟩ := mem_iUnion.1 hg
      obtain ⟨_, ⟨α, rfl⟩, rfl⟩ := (mem_basepointChangeSubgroup _ _ _).1 hg
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1
        (map_fst_fundamentalGroupMulEquivOfPath_map_graphTorus_mem_zpowers (hh k) (ψ k) α)
      rw [← hn]
      refine zpow_mem (Subgroup.subset_normalClosure ?_) n
      exact ⟨k, rfl⟩
    · obtain ⟨_, ⟨β, rfl⟩, rfl⟩ := (mem_basepointChangeSubgroup _ _ _).1 hg
      rw [map_fst_fundamentalGroupMulEquivOfPath_map_graphTorus_const]
      exact one_mem _

/-- **Killing graph tori of loops and a fibre torus in `π₁(M × T)`.** Let `h k`, for `k` in a
type `κ`, be smooth circle maps into `M` whose loops, brought to `x` along any paths, normally
generate the same subgroup of `π₁(M, x)` as loops `γ k` at `x`, and let `z` be a point of `M`.
Then `π₁(M × T, (x, y))`, modulo the normal closure of the images of `π₁(T, 0)` under the graph
tori of the `h k` and under the fibre torus `{z} × T`, each brought to `(x, y)` along a path, is
`π₁(M, x)` modulo the normal closure of the `γ k`. The isomorphism is induced by the first
projection (`graphTorusQuotientMulEquiv_mk`).

The hypotheses on `h` and `z` are in the form in which `exists_graphTorus_family` provides
them. -/
noncomputable def graphTorusQuotientMulEquiv {κ : Type*} {x : M} {y : ∀ j, AddCircle (p j)}
    (γ : κ → Path x x) {h : κ → C(AddCircle (p i), M)} (hh : ∀ k, ContMDiff 𝓘(ℝ) I ∞ (h k))
    (hγ : ∀ χ : ∀ k, Path x (h k 0),
      Subgroup.normalClosure (range fun k ↦ fromPath (.mk ((χ k).trans
        ((h k).toLoop.trans (χ k).symm)))) =
        Subgroup.normalClosure (range fun k ↦ fromPath (.mk (γ k))))
    (z : M) (ψ : ∀ k, Path (graphTorus (hh k) 0) (x, y))
    (φ : Path (graphTorus (contMDiff_const : ContMDiff 𝓘(ℝ) I ∞ fun _ : AddCircle (p i) ↦ z) 0)
      (x, y)) :
    FundamentalGroup (M × ∀ j, AddCircle (p j)) (x, y) ⧸
        Subgroup.normalClosure
          ((⋃ k, (basepointChangeSubgroup (ψ k) (map (graphTorus (hh k)).toContinuousMap 0).range :
            Set (FundamentalGroup (M × ∀ j, AddCircle (p j)) (x, y)))) ∪
            basepointChangeSubgroup φ
              (map (graphTorus contMDiff_const).toContinuousMap 0).range) ≃*
      FundamentalGroup M x ⧸ Subgroup.normalClosure (range fun k ↦ fromPath (.mk (γ k))) :=
  QuotientGroup.liftEquiv _
    (φ := (QuotientGroup.mk' _).comp ((MonoidHom.fst _ _).comp (prodMulEquiv x y).toMonoidHom))
    ((QuotientGroup.mk'_surjective _).comp
      (Prod.fst_surjective.comp (prodMulEquiv x y).surjective))
    (by rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      comap_map_fst_normalClosure_eq_normalClosure_graphTorus γ hh hγ z ψ φ])

/-- `graphTorusQuotientMulEquiv` sends the class of `g` to the class of its first coordinate. -/
@[simp]
theorem graphTorusQuotientMulEquiv_mk {κ : Type*} {x : M} {y : ∀ j, AddCircle (p j)}
    (γ : κ → Path x x) {h : κ → C(AddCircle (p i), M)} (hh : ∀ k, ContMDiff 𝓘(ℝ) I ∞ (h k))
    (hγ : ∀ χ : ∀ k, Path x (h k 0),
      Subgroup.normalClosure (range fun k ↦ fromPath (.mk ((χ k).trans
        ((h k).toLoop.trans (χ k).symm)))) =
        Subgroup.normalClosure (range fun k ↦ fromPath (.mk (γ k))))
    (z : M) (ψ : ∀ k, Path (graphTorus (hh k) 0) (x, y))
    (φ : Path (graphTorus (contMDiff_const : ContMDiff 𝓘(ℝ) I ∞ fun _ : AddCircle (p i) ↦ z) 0)
      (x, y)) (g : FundamentalGroup (M × ∀ j, AddCircle (p j)) (x, y)) :
    graphTorusQuotientMulEquiv γ hh hγ z ψ φ g =
      ((prodMulEquiv x y g).1 :
        FundamentalGroup M x ⧸ Subgroup.normalClosure (range fun k ↦ fromPath (.mk (γ k)))) := by
  rw [graphTorusQuotientMulEquiv, QuotientGroup.liftEquiv_mk, MonoidHom.comp_apply,
    MonoidHom.comp_apply, QuotientGroup.mk'_apply, MulEquiv.coe_toMonoidHom, MonoidHom.coe_fst]

end FundamentalGroup

end GeneralPosition

/-! ### `M × T` on a vector-space model -/

section OnModel

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [I.Boundaryless] (M : Type*) [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {ι : Type*} [Fintype ι] (p : ι ⊕ ι → ℝ)
  [∀ i, Fact (0 < p i)] {i : ι ⊕ ι} {h h' : AddCircle (p i) → M}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : (E × (ι ⊕ ι → ℝ)) ≃L[ℝ] V)

/-- The product `M × T` of a boundaryless manifold `M`, modelled on `I`, and the torus
`T = ∀ i : ι ⊕ ι, AddCircle (p i)`, charted on the real normed space `V`: its product charts,
followed by the product model `I.prod (ModelWithCorners.pi fun _ ↦ 𝓘(ℝ))`
(`TauCeti.BoundarylessModel`) and by a real linear isomorphism
`L : E × (ι ⊕ ι → ℝ) ≃L[ℝ] V` (`SymplecticGeometry.Remodel`). -/
abbrev ProdTorusOnModel : Type _ :=
  Remodel L.toDiffeomorph (BoundarylessModel (I.prod (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)))
    (M × ∀ i, AddCircle (p i)))

namespace ProdTorusOnModel

variable {M p}

/-- The identification of `M × T` with `ProdTorusOnModel I M p L`: the identity of the points, a
smooth diffeomorphism from the product model to the model `V`. -/
def diffeomorph :
    (M × ∀ i, AddCircle (p i)) ≃ₘ⟮I.prod (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)), 𝓘(ℝ, V)⟯
      ProdTorusOnModel I M p L :=
  (BoundarylessModel.diffeomorph _ ∞).trans (remodelDiffeomorph _ _)

omit [IsManifold I ∞ M] in
theorem diffeomorph_def :
    diffeomorph I L =
      (BoundarylessModel.diffeomorph (I.prod (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)))
        (M := M × ∀ i, AddCircle (p i)) ∞).trans (remodelDiffeomorph L.toDiffeomorph _) :=
  (rfl)

omit [IsManifold I ∞ M] in
@[simp]
theorem coe_diffeomorph :
    ⇑(diffeomorph I L) = remodelHomeomorph _ _ ∘ BoundarylessModel.homeomorph
      (I.prod (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))) (M × ∀ i, AddCircle (p i)) := by
  rw [diffeomorph_def, Diffeomorph.coe_trans, coe_remodelDiffeomorph,
    BoundarylessModel.coe_diffeomorph]

omit [IsManifold I ∞ M] in
@[simp]
theorem coe_diffeomorph_symm :
    ⇑(diffeomorph I L).symm = (BoundarylessModel.homeomorph
      (I.prod (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))) (M × ∀ i, AddCircle (p i))).symm ∘
        (remodelHomeomorph _ _).symm := by
  rw [diffeomorph_def, Diffeomorph.symm_trans', Diffeomorph.coe_trans,
    coe_remodelDiffeomorph_symm, BoundarylessModel.coe_diffeomorph_symm]

/-- The product form `pr₁^* σ + pr₂^* ω_T` of a two-form `σ` on `M` and of the standard form
`ω_T = TauCeti.torusSymplecticForm p` of the torus, moved to `ProdTorusOnModel I M p L` along
`ProdTorusOnModel.diffeomorph`. -/
def prodForm (σ : SmoothTwoForm I M) : SmoothTwoForm 𝓘(ℝ, V) (ProdTorusOnModel I M p L) :=
  SmoothForm.mpullback (diffeomorph I L).symm (diffeomorph I L).symm.contMDiff
    (SmoothTwoForm.prod σ (torusSymplecticForm p))

theorem prodForm_def (σ : SmoothTwoForm I M) :
    prodForm I L σ =
      SmoothForm.mpullback (diffeomorph I L).symm (diffeomorph I L).symm.contMDiff
        (SmoothTwoForm.prod σ (torusSymplecticForm p)) :=
  (rfl)

/-- Pulled back along `ProdTorusOnModel.diffeomorph`, the form of `ProdTorusOnModel I M p L` is
the product form `pr₁^* σ + pr₂^* ω_T` of `M × T`. -/
theorem mpullback_diffeomorph_prodForm (σ : SmoothTwoForm I M) :
    SmoothForm.mpullback (diffeomorph I L) (diffeomorph I L).contMDiff (prodForm I L σ) =
      SmoothTwoForm.prod σ (torusSymplecticForm p) := by
  rw [prodForm_def]
  exact SmoothForm.mpullback_mpullback_symm _ _

/-- For a nondegenerate two-form `σ` on `M`, the product form of `ProdTorusOnModel I M p L` is
nondegenerate. -/
theorem isNondegenerate_prodForm {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate) :
    (prodForm (p := p) I L σ).IsNondegenerate :=
  (hσ.prod (isSymplectic_torusSymplecticForm p).isNondegenerate
    ).isNondegenerate_mpullback_of_isLocalDiffeomorph (diffeomorph I L).symm.isLocalDiffeomorph

/-- For a symplectic form `σ` on `M`, such as an area form of a surface, the product form of
`ProdTorusOnModel I M p L` is symplectic. -/
theorem isSymplectic_prodForm {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic) :
    (prodForm (p := p) I L σ).IsSymplectic :=
  ((diffeomorph I L).symm.isLocalDiffeomorph.isSymplectic_mpullback_iff
      (diffeomorph I L).symm.surjective).2
    (hσ.prod (isSymplectic_torusSymplecticForm p))

omit [Fintype ι] in
include L in
/-- When `E` has dimension two, as for a surface `M`, the torus `∀ i : ι ⊕ ι, AddCircle (p i)`
has codimension two in `ProdTorusOnModel I M p L`. -/
theorem finrank_complex_eq_finrank_sub [Finite ι] (hE : finrank ℝ E = 2) :
    finrank ℝ ℂ = finrank ℝ V - finrank ℝ (ι ⊕ ι → ℝ) := by
  have := Fintype.ofFinite ι
  rw [← L.toLinearEquiv.finrank_eq]
  exact Complex.finrank_real_eq_finrank_prod_sub hE

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ V]

/-- The graph torus `x ↦ (h (x i), x)` of a smooth circle map `h : AddCircle (p i) → M`
(`SymplecticGeometry.graphTorus`), followed by `ProdTorusOnModel.diffeomorph`, as an embedding of
the torus into `ProdTorusOnModel I M p L`. For a constant map `h` it is the fibre torus
`{z} × T`. -/
def graphTorus (hh : ContMDiff 𝓘(ℝ) I ∞ h) :
    SmoothEmbedding (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) 𝓘(ℝ, V) ∞
      (∀ i, AddCircle (p i)) (ProdTorusOnModel I M p L) :=
  (SymplecticGeometry.graphTorus hh).transDiffeomorphOfBoundaryless (diffeomorph I L) (by simp)

theorem graphTorus_def (hh : ContMDiff 𝓘(ℝ) I ∞ h) :
    graphTorus I L hh =
      (SymplecticGeometry.graphTorus hh).transDiffeomorphOfBoundaryless (diffeomorph I L)
        (by simp) :=
  (rfl)

/-- The embedded torus is `ProdTorusOnModel.diffeomorph ∘ SymplecticGeometry.graphTorus hh`. -/
@[simp]
theorem coe_graphTorus (hh : ContMDiff 𝓘(ℝ) I ∞ h) :
    ⇑(graphTorus I L hh) = diffeomorph I L ∘ SymplecticGeometry.graphTorus hh := by
  rw [graphTorus_def, SmoothEmbedding.coe_transDiffeomorphOfBoundaryless]

/-- The image of the embedded torus is that of the graph torus of `h` in `M × T`. -/
theorem range_graphTorus (hh : ContMDiff 𝓘(ℝ) I ∞ h) :
    range (graphTorus I L hh) = diffeomorph I L '' range (SymplecticGeometry.graphTorus hh) := by
  rw [coe_graphTorus, range_comp]

/-- Two embedded tori are disjoint exactly when the graph tori in `M × T` are. -/
theorem disjoint_range_graphTorus_iff (hh : ContMDiff 𝓘(ℝ) I ∞ h) (hh' : ContMDiff 𝓘(ℝ) I ∞ h') :
    Disjoint (range (graphTorus I L hh)) (range (graphTorus I L hh')) ↔
      Disjoint (range (SymplecticGeometry.graphTorus hh))
        (range (SymplecticGeometry.graphTorus hh')) := by
  rw [range_graphTorus, range_graphTorus]
  exact disjoint_image_iff (diffeomorph I L).injective

/-- The embedded torus pulls the form of `ProdTorusOnModel I M p L` back to the standard
symplectic form `TauCeti.torusSymplecticForm p` of the torus, whatever the two-form `σ`. -/
theorem mpullback_graphTorus_prodForm (hh : ContMDiff 𝓘(ℝ) I ∞ h)
    (σ : SmoothTwoForm I M) :
    SmoothForm.mpullback (graphTorus I L hh) (graphTorus I L hh).contMDiff
      (prodForm I L σ) = torusSymplecticForm p := by
  rw [graphTorus_def, SmoothEmbedding.mpullback_transDiffeomorphOfBoundaryless _ _ _
    (mpullback_diffeomorph_prodForm I L σ), mpullback_graphTorus_prod_torusSymplecticForm hh σ]

/-- For a nondegenerate two-form `σ` on `M`, the embedded torus has symplectic tangent images for
the product form of `ProdTorusOnModel I M p L`. -/
theorem hasSymplecticTangentImages_graphTorus {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate)
    (hh : ContMDiff 𝓘(ℝ) I ∞ h) :
    (isNondegenerate_prodForm (p := p) I L hσ).HasSymplecticTangentImages
      (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) (graphTorus I L hh) := by
  rw [graphTorus_def]
  exact (SmoothEmbedding.hasSymplecticTangentImages_transDiffeomorphOfBoundaryless_iff _
    (diffeomorph I L) _ (mpullback_diffeomorph_prodForm I L σ)).2
    (SymplecticGeometry.hasSymplecticTangentImages_graphTorus hσ hh)

/-- **The embedded tori are symplectically framed.** For a nondegenerate two-form `σ` on a
Hausdorff σ-compact surface `M`, the embedded graph torus of a smooth circle map `h` has a
symplectic framing for the product form of `ProdTorusOnModel I M p L`: a framing of the graph
torus in `M × T` (`SymplecticGeometry.nonempty_symplecticFraming_graphTorus`), moved along
`ProdTorusOnModel.diffeomorph` (`SymplecticFraming.transDiffeomorph`). -/
theorem nonempty_symplecticFraming_graphTorus [T2Space M] [SigmaCompactSpace M]
    {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate)
    (hh : ContMDiff 𝓘(ℝ) I ∞ h) (hE : finrank ℝ E = 2) :
    Nonempty (SymplecticFraming (hasSymplecticTangentImages_graphTorus I L hσ hh)
      (finrank_complex_eq_finrank_sub L hE)) := by
  obtain ⟨Φ⟩ := SymplecticGeometry.nonempty_symplecticFraming_graphTorus hσ hh hE
  exact ⟨Φ.transDiffeomorph (diffeomorph I L) (isNondegenerate_prodForm I L hσ)
    (mpullback_diffeomorph_prodForm I L σ) (finrank_complex_eq_finrank_sub L hE)⟩

open FundamentalGroup in
/-- The isomorphism `π₁(M × T, x) ≃* π₁(ProdTorusOnModel I M p L, x)` of the homeomorphism
`ProdTorusOnModel.diffeomorph` maps the normal closure of the images of `π₁(T, 0)` under the
graph tori of the `f k` in `M × T`, each brought to `x` along a path `ψ k`, onto the normal
closure of their images under the embedded tori in `ProdTorusOnModel I M p L`, each brought to
`x` along any path `ψ' k`. -/
theorem map_normalClosure_basepointChangeSubgroup_graphTorus {κ : Type*}
    {f : κ → AddCircle (p i) → M} (hf : ∀ k, ContMDiff 𝓘(ℝ) I ∞ (f k))
    {x : M × ∀ j, AddCircle (p j)} (ψ : ∀ k, Path (SymplecticGeometry.graphTorus (hf k) 0) x)
    (ψ' : ∀ k, Path (graphTorus I L (hf k) 0) ((diffeomorph I L).toHomeomorph x)) :
    (Subgroup.normalClosure (⋃ k, (basepointChangeSubgroup (ψ k)
        (map (SymplecticGeometry.graphTorus (hf k)).toContinuousMap 0).range :
          Set (FundamentalGroup (M × ∀ j, AddCircle (p j)) x)))).map
      (homeomorphMulEquiv (diffeomorph I L).toHomeomorph x).toMonoidHom =
    Subgroup.normalClosure (⋃ k, (basepointChangeSubgroup (ψ' k)
        (map (graphTorus I L (hf k)).toContinuousMap 0).range :
          Set (FundamentalGroup (ProdTorusOnModel I M p L)
            ((diffeomorph I L).toHomeomorph x)))) := by
  have hD : (homeomorphMulEquiv (diffeomorph I L).toHomeomorph x).toMonoidHom =
      map ((diffeomorph I L (M := M) (p := p)).toHomeomorph :
        C(M × ∀ j, AddCircle (p j), ProdTorusOnModel I M p L)) x := by
    ext q
    rw [MulEquiv.coe_toMonoidHom, homeomorphMulEquiv_apply, mapOfEq_rfl]
  have hk : ∀ k, (graphTorus I L (hf k)).toContinuousMap =
      ((diffeomorph I L (M := M) (p := p)).toHomeomorph :
        C(M × ∀ j, AddCircle (p j), ProdTorusOnModel I M p L)).comp
        (SymplecticGeometry.graphTorus (hf k)).toContinuousMap := fun k ↦ by
    ext t
    simp
  rw [hD, Subgroup.map_normalClosure _ _
    (hD ▸ (homeomorphMulEquiv (diffeomorph I L).toHomeomorph x).surjective), eq_comm]
  refine (Subgroup.normalClosure_iUnion_congr fun k ↦
    normalClosure_basepointChangeSubgroup_range_eq_of_eq_comp _ _ (hk k) _ (ψ k)).trans ?_
  simp only [Subgroup.coe_map, image_iUnion]

end ProdTorusOnModel

end OnModel

-- The instances that the fibre sum asks of its pieces, for the closed surface of genus `g`.
section ClosedSurface

variable {ι : Type*} [Fintype ι] (p : ι ⊕ ι → ℝ) [∀ i, Fact (0 < p i)]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (L : (EuclideanSpace ℝ (Fin 2) × (ι ⊕ ι → ℝ)) ≃L[ℝ] V) (g : ℕ)

example : IsManifold 𝓘(ℝ, V) ∞ (ProdTorusOnModel (𝓡 2) (ClosedSurface g) p L) := inferInstance
example : CompactSpace (ProdTorusOnModel (𝓡 2) (ClosedSurface g) p L) := inferInstance
example : ConnectedSpace (ProdTorusOnModel (𝓡 2) (ClosedSurface g) p L) := inferInstance
example : T2Space (ProdTorusOnModel (𝓡 2) (ClosedSurface g) p L) := inferInstance
example : SecondCountableTopology (ProdTorusOnModel (𝓡 2) (ClosedSurface g) p L) := inferInstance
example : BoundarylessManifold 𝓘(ℝ, V) (ProdTorusOnModel (𝓡 2) (ClosedSurface g) p L) :=
  inferInstance

-- The model `Fin 2 → ℂ` of the rational elliptic surface (`rationalEllipticSurface.OnModel`) is
-- one such `V`.
example : Nonempty ((EuclideanSpace ℝ (Fin 2) × (Unit ⊕ Unit → ℝ)) ≃L[ℝ] (Fin 2 → ℂ)) :=
  ⟨ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_pi_fintype])⟩

-- With an area form of the surface, each graph torus is symplectic and framed.
example [FiniteDimensional ℝ V] {i : ι ⊕ ι} {h : AddCircle (p i) → ClosedSurface g}
    (hh : ContMDiff 𝓘(ℝ) (𝓡 2) ∞ h) :
    ∃ (σ : SmoothTwoForm (𝓡 2) (ClosedSurface g)) (hσ : σ.IsSymplectic),
      Nonempty (SymplecticFraming
        (ProdTorusOnModel.hasSymplecticTangentImages_graphTorus (𝓡 2) L hσ.isNondegenerate hh)
        (ProdTorusOnModel.finrank_complex_eq_finrank_sub L finrank_euclideanSpace_fin)) := by
  obtain ⟨σ, hσ⟩ := ClosedSurface.exists_isSymplectic g
  exact ⟨σ, hσ, ProdTorusOnModel.nonempty_symplecticFraming_graphTorus _ _ hσ.isNondegenerate hh
    finrank_euclideanSpace_fin⟩

end ClosedSurface

/-! ### The realization of finitely presented groups -/

section Realization

open FundamentalGroup TauCeti.SurfaceGroup.Orientable

/-- Let `γ k`, for `k : Fin g ⊕ Fin r`, be loops at the base point of the closed surface of
genus `g` whose classes correspond, under `ClosedSurface.fundamentalGroupMulEquiv g`, to the
generators `b k` and to the words `w j` read in the generators `a k`. Then `π₁` of the surface
modulo the normal closure of the classes of the `γ k` is the group presented by `g` letters and
the relators `w j`. -/
private def closedSurfaceQuotientMulEquiv {g r : ℕ} (w : Fin r → FreeGroup (Fin g))
    (γ : Fin g ⊕ Fin r → Path (ClosedSurface.basePoint g) (ClosedSurface.basePoint g))
    (hγ : ∀ k, ClosedSurface.fundamentalGroupMulEquiv g (fromPath (.mk (γ k))) =
      Sum.elim (b g 0) (fun j ↦ FreeGroup.lift (a g 0) (w j)) k) :
    FundamentalGroup (ClosedSurface g) (ClosedSurface.basePoint g) ⧸
        Subgroup.normalClosure (range fun k ↦ fromPath (.mk (γ k))) ≃*
      PresentedGroup (range w) :=
  (QuotientGroup.congr _ (bWordsNormalClosure w) (ClosedSurface.fundamentalGroupMulEquiv g) (by
    rw [Subgroup.map_normalClosure _ _ (ClosedSurface.fundamentalGroupMulEquiv g).surjective,
      bWordsNormalClosure_def, ← range_comp, ← Set.Sum.elim_range]
    exact congrArg _ (congrArg range (funext hγ)))).trans (quotientEquivPresentedGroup w)

/-- **Gompf's realization of finitely presented groups.** Every finitely presented group `G` is
isomorphic to the fundamental group, at any base point, of a compact, connected, Hausdorff
symplectic manifold `M` of real dimension four, smooth and without boundary.

Milestone: *Gompf's realization of finitely presented groups*. -/
theorem exists_fundamentalGroup_mulEquiv (G : Type*) [Group G] [Group.IsFinitelyPresented G] :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (EuclideanSpace ℝ (Fin 4)) M)
      (_ : IsManifold (𝓡 4) ∞ M), T2Space M ∧ CompactSpace M ∧ ConnectedSpace M ∧
      (∃ τ : SmoothTwoForm (𝓡 4) M, τ.IsSymplectic) ∧
      ∀ y : M, Nonempty (G ≃* FundamentalGroup M y) := by
  obtain ⟨g, r, -, w, ⟨eG⟩⟩ := Group.IsFinitelyPresented.exists_one_le_mulEquiv_presentedGroup G
  -- Loops on the surface realizing the generators `b k` and the relators `w j`.
  let γ : Fin g ⊕ Fin r → Path (ClosedSurface.basePoint g) (ClosedSurface.basePoint g) :=
    fun k ↦ Quotient.out (toPath ((ClosedSurface.fundamentalGroupMulEquiv g).symm
      (Sum.elim (b g 0) (fun j ↦ FreeGroup.lift (a g 0) (w j)) k)))
  have hγ : ∀ k, ClosedSurface.fundamentalGroupMulEquiv g (fromPath (.mk (γ k))) =
      Sum.elim (b g 0) (fun j ↦ FreeGroup.lift (a g 0) (w j)) k := fun k ↦ by simp [γ]
  -- Their graph tori in `F × T²`, in general position, and a fibre torus missing them.
  obtain ⟨p, hp⟩ : ∃ p : Unit ⊕ Unit → ℝ, ∀ i, 0 < p i := ⟨fun _ ↦ 1, fun _ ↦ one_pos⟩
  have : ∀ i, Fact (0 < p i) := fun i ↦ ⟨hp i⟩
  obtain ⟨h, hh, z, -, hN, hdisj, hz⟩ := exists_graphTorus_family (I := 𝓡 2) (p := p)
    (i := .inl ()) (by simp) γ
  obtain ⟨σ, hσ⟩ := ClosedSurface.exists_isSymplectic g
  -- The circle maps, with the constant map at `z` for the fibre torus.
  let hO : Option (Fin g ⊕ Fin r) → AddCircle (p (.inl ())) → ClosedSurface g :=
    fun o ↦ o.elim (fun _ ↦ z) fun k ↦ h k
  have hhO : ∀ o, ContMDiff 𝓘(ℝ) (𝓡 2) ∞ (hO o) := by
    rintro (_ | k)
    exacts [contMDiff_const, hh k]
  -- `F × T²` on the model of the rational elliptic surface.
  let L : (EuclideanSpace ℝ (Fin 2) × (Unit ⊕ Unit → ℝ)) ≃L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  let e : (Fin 2 → ℂ) ≃L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_pi_fintype])
  let ι := fun o ↦ ProdTorusOnModel.graphTorus (𝓡 2) L (hhO o)
  have hι : ∀ o, (ProdTorusOnModel.isSymplectic_prodForm (p := p) (𝓡 2) L
      hσ).isNondegenerate.HasSymplecticTangentImages
        (ModelWithCorners.pi fun _ : Unit ⊕ Unit ↦ 𝓘(ℝ)) (ι o) := fun o ↦
    ProdTorusOnModel.hasSymplecticTangentImages_graphTorus _ _ hσ.isNondegenerate (hhO o)
  let Φ : ∀ o, SymplecticFraming (hι o)
      (ProdTorusOnModel.finrank_complex_eq_finrank_sub L finrank_euclideanSpace_fin) := fun o ↦
    Classical.choice (ProdTorusOnModel.nonempty_symplecticFraming_graphTorus _ _
      hσ.isNondegenerate (hhO o) finrank_euclideanSpace_fin)
  have hdisjι : Pairwise fun o o' ↦ Disjoint (range (ι o)) (range (ι o')) := by
    rintro (_ | k) (_ | l) hkl
    · exact absurd rfl hkl
    · exact ((ProdTorusOnModel.disjoint_range_graphTorus_iff _ _ _ _).2 (hz l)).symm
    · exact (ProdTorusOnModel.disjoint_range_graphTorus_iff _ _ _ _).2 (hz k)
    · exact (ProdTorusOnModel.disjoint_range_graphTorus_iff _ _ _ _).2
        (hdisj fun hkl' ↦ hkl (congrArg some hkl'))
  -- The sums with the rational elliptic surface.
  obtain ⟨Y, _, _, _, hY₁, hY₂, hY₃, hY₄, hπ⟩ := exists_fundamentalGroup_mulEquiv_quotient_tori e p
    _ (ProdTorusOnModel.isSymplectic_prodForm (p := p) (𝓡 2) L hσ) ι hι
    (fun o ↦ ProdTorusOnModel.mpullback_graphTorus_prodForm _ _ _ σ) Φ hdisjι
  refine ⟨Y, _, _, _, hY₁, hY₂, hY₃, hY₄, fun y ↦ ?_⟩
  -- Compare the quotient of `π₁` of the model with that of `F × T²`.
  let D := (ProdTorusOnModel.diffeomorph (𝓡 2) (M := ClosedSurface g) (p := p) L).toHomeomorph
  let x₀ : ClosedSurface g × ∀ i, AddCircle (p i) := (ClosedSurface.basePoint g, 0)
  have := ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 4))
    (ProdTorusOnModel (𝓡 2) (ClosedSurface g) p L)
  have : PathConnectedSpace (ProdTorusOnModel (𝓡 2) (ClosedSurface g) p L) :=
    pathConnectedSpace_iff_connectedSpace.2 inferInstance
  have : PathConnectedSpace (ClosedSurface g × ∀ i, AddCircle (p i)) :=
    D.symm.surjective.pathConnectedSpace D.symm.continuous
  let ψ : ∀ o, Path (SymplecticGeometry.graphTorus (hhO o) 0) x₀ := fun o ↦
    PathConnectedSpace.somePath _ _
  obtain ⟨eY⟩ := hπ 0 (D x₀) y fun o ↦ PathConnectedSpace.somePath _ _
  have hmap := ProdTorusOnModel.map_normalClosure_basepointChangeSubgroup_graphTorus (𝓡 2) L hhO
    ψ fun o ↦ PathConnectedSpace.somePath (ι o 0) (D x₀)
  rw [iUnion_option, union_comm] at hmap
  exact ⟨(eG.trans ((closedSurfaceQuotientMulEquiv w γ hγ).symm.trans
    ((graphTorusQuotientMulEquiv γ hh hN z (fun k ↦ ψ (some k)) (ψ none)).symm.trans
      (QuotientGroup.congr _ _ (homeomorphMulEquiv D x₀) hmap)))).trans eY.symm⟩

end Realization

end SymplecticGeometry

end

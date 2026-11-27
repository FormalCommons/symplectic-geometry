/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.ModelTransport.ModelWithCorners
public import SymplecticGeometry.Geometry.Manifold.ModelTransport.Remodel
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Diffeomorph
public import SymplecticGeometry.Geometry.Symplectic.Sum.GraphTorus
public import SymplecticGeometry.Topology.Homotopy.AddCircle
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.AddCircle
import SymplecticGeometry.Geometry.Manifold.GeneralPosition
import SymplecticGeometry.Geometry.Manifold.Instances.Surface.Orientation
import SymplecticGeometry.Geometry.Manifold.NullSet

/-!
# Disjoint symplectic tori in `Σ × T` for finitely many loops

This file prepares the realization of finitely presented groups as fundamental groups of closed
symplectic four-manifolds. Let `Σ` be a Hausdorff manifold of dimension at least two, smooth and
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

To sum `Σ × T` with the rational elliptic surface, both must be charted on one model, and
`rationalEllipticSurface.OnModel e` is charted on a real normed space `V`. So `Σ × T`, modelled on
the product of the model `I` of `Σ` and of the model of the torus, is moved to the model
`𝓘(ℝ, V)` along that product model (`ModelWithCorners.toDiffeomorph`) and a real linear
isomorphism `L : E × (ι ⊕ ι → ℝ) ≃L[ℝ] V` (`SymplecticGeometry.Remodel`); for the closed surface
and `T = T²`, `V = Fin 2 → ℂ` is one choice. The product form, the graph tori, their framings and
their disjointness all move along the identity of the points
(`SymplecticGeometry.ProdTorusOnModel.diffeomorph`), and the copy keeps the compactness,
connectedness and separation of `Σ × T`.

## Main definitions

* `SymplecticGeometry.ProdTorusOnModel I M p L`: the product `M × T`, charted on `V`.
* `SymplecticGeometry.ProdTorusOnModel.symplecticForm`: the product form `pr₁^* σ + pr₂^* ω_T` on
  it, symplectic for a symplectic `σ`
  (`SymplecticGeometry.ProdTorusOnModel.isSymplectic_symplecticForm`).
* `SymplecticGeometry.ProdTorusOnModel.graphTorus`: the graph torus of a circle map in it, with
  symplectic tangent images
  (`SymplecticGeometry.ProdTorusOnModel.hasSymplecticTangentImages_graphTorus`) and, on a
  surface, a symplectic framing
  (`SymplecticGeometry.ProdTorusOnModel.nonempty_symplecticFraming_graphTorus`).

## Main results

* `SymplecticGeometry.exists_graphTorus_family`: smooth loops in general position, homotopic to
  given loops, whose graph tori are pairwise disjoint and miss a fibre torus.
* `SymplecticGeometry.ProdTorusOnModel.mpullback_graphTorus_symplecticForm`: the graph tori in
  `ProdTorusOnModel I M p L` pull its form back to `ω_T`.
* `SymplecticGeometry.ProdTorusOnModel.disjoint_range_graphTorus_iff`: they are disjoint exactly
  when the graph tori in `M × T` are.

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
(`ModelWithCorners.toDiffeomorph`) and by a real linear isomorphism
`L : E × (ι ⊕ ι → ℝ) ≃L[ℝ] V` (`SymplecticGeometry.Remodel`). -/
abbrev ProdTorusOnModel : Type _ :=
  Remodel (((I.prod (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))).toDiffeomorph ∞).trans
    L.toDiffeomorph) (M × ∀ i, AddCircle (p i))

namespace ProdTorusOnModel

variable {M p}

/-- The identification of `M × T` with `ProdTorusOnModel I M p L`: the identity of the points, a
smooth diffeomorphism from the product model to the model `V`. -/
def diffeomorph :
    (M × ∀ i, AddCircle (p i)) ≃ₘ⟮I.prod (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)), 𝓘(ℝ, V)⟯
      ProdTorusOnModel I M p L :=
  remodelDiffeomorph _ _

omit [IsManifold I ∞ M] in
theorem diffeomorph_def : diffeomorph I L = remodelDiffeomorph _ (M × ∀ i, AddCircle (p i)) :=
  (rfl)

omit [IsManifold I ∞ M] in
@[simp]
theorem coe_diffeomorph : ⇑(diffeomorph I L) = remodelHomeomorph _ (M × ∀ i, AddCircle (p i)) := by
  rw [diffeomorph_def, coe_remodelDiffeomorph]

omit [IsManifold I ∞ M] in
@[simp]
theorem coe_diffeomorph_symm :
    ⇑(diffeomorph I L).symm = (remodelHomeomorph _ (M × ∀ i, AddCircle (p i))).symm := by
  rw [diffeomorph_def, coe_remodelDiffeomorph_symm]

/-- The product form `pr₁^* σ + pr₂^* ω_T` of a two-form `σ` on `M` and of the standard form
`ω_T = TauCeti.torusSymplecticForm p` of the torus, moved to `ProdTorusOnModel I M p L` along
`ProdTorusOnModel.diffeomorph`. -/
def symplecticForm (σ : SmoothTwoForm I M) : SmoothTwoForm 𝓘(ℝ, V) (ProdTorusOnModel I M p L) :=
  SmoothForm.mpullback (diffeomorph I L).symm (diffeomorph I L).symm.contMDiff
    (SmoothTwoForm.prod σ (torusSymplecticForm p))

theorem symplecticForm_def (σ : SmoothTwoForm I M) :
    symplecticForm I L σ =
      SmoothForm.mpullback (diffeomorph I L).symm (diffeomorph I L).symm.contMDiff
        (SmoothTwoForm.prod σ (torusSymplecticForm p)) :=
  (rfl)

/-- Pulled back along `ProdTorusOnModel.diffeomorph`, the form of `ProdTorusOnModel I M p L` is
the product form `pr₁^* σ + pr₂^* ω_T` of `M × T`. -/
theorem mpullback_diffeomorph_symplecticForm (σ : SmoothTwoForm I M) :
    SmoothForm.mpullback (diffeomorph I L) (diffeomorph I L).contMDiff (symplecticForm I L σ) =
      SmoothTwoForm.prod σ (torusSymplecticForm p) := by
  rw [symplecticForm_def]
  exact SmoothForm.mpullback_mpullback_symm _ _

/-- For a symplectic form `σ` on `M`, such as an area form of a surface, the form of
`ProdTorusOnModel I M p L` is symplectic. -/
theorem isSymplectic_symplecticForm {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic) :
    (symplecticForm (p := p) I L σ).IsSymplectic :=
  ((diffeomorph I L).symm.isLocalDiffeomorph.isSymplectic_mpullback_iff
      (diffeomorph I L).symm.surjective).2
    (hσ.prod (isSymplectic_torusSymplecticForm p))

omit [Fintype ι] in
include L in
/-- When `E` has dimension two, as for a surface `M`, the torus `∀ i : ι ⊕ ι, AddCircle (p i)`
has codimension two in `ProdTorusOnModel I M p L`. -/
theorem finrank_complex_eq_finrank_sub [Finite ι] [FiniteDimensional ℝ E] (hE : finrank ℝ E = 2) :
    finrank ℝ ℂ = finrank ℝ V - finrank ℝ (ι ⊕ ι → ℝ) := by
  have := Fintype.ofFinite ι
  rw [← L.toLinearEquiv.finrank_eq, finrank_prod, hE]
  simp

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
theorem mpullback_graphTorus_symplecticForm (hh : ContMDiff 𝓘(ℝ) I ∞ h)
    (σ : SmoothTwoForm I M) :
    SmoothForm.mpullback (graphTorus I L hh) (graphTorus I L hh).contMDiff
      (symplecticForm I L σ) = torusSymplecticForm p := by
  rw [← mpullback_graphTorus_prod_torusSymplecticForm hh σ,
    ← mpullback_diffeomorph_symplecticForm I L σ, SmoothForm.mpullback_mpullback]
  exact SmoothForm.mpullback_congr _ _ (coe_graphTorus I L hh) _

/-- For a symplectic form `σ` on `M`, the embedded torus has symplectic tangent images for the
form of `ProdTorusOnModel I M p L`. -/
theorem hasSymplecticTangentImages_graphTorus {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
    (hh : ContMDiff 𝓘(ℝ) I ∞ h) :
    (isSymplectic_symplecticForm (p := p) I L hσ).isNondegenerate.HasSymplecticTangentImages
      (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) (graphTorus I L hh) := by
  rw [coe_graphTorus]
  exact (SmoothTwoForm.IsNondegenerate.hasSymplecticTangentImages_diffeomorph_comp_iff
    (diffeomorph I L) (mpullback_diffeomorph_symplecticForm I L σ)).2
    (SymplecticGeometry.hasSymplecticTangentImages_graphTorus hσ.isNondegenerate hh)

/-- **The embedded tori are symplectically framed.** For a symplectic form `σ` on a Hausdorff
σ-compact surface `M`, the embedded graph torus of a smooth circle map `h` has a symplectic framing
for the form of `ProdTorusOnModel I M p L`: a framing of the graph torus in `M × T`
(`SymplecticGeometry.nonempty_symplecticFraming_graphTorus`), moved along
`ProdTorusOnModel.diffeomorph` (`SymplecticFraming.transDiffeomorph`). -/
theorem nonempty_symplecticFraming_graphTorus [T2Space M] [SigmaCompactSpace M]
    {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
    (hh : ContMDiff 𝓘(ℝ) I ∞ h) (hE : finrank ℝ E = 2) :
    Nonempty (SymplecticFraming (hasSymplecticTangentImages_graphTorus I L hσ hh)
      (finrank_complex_eq_finrank_sub L hE)) := by
  obtain ⟨Φ⟩ := SymplecticGeometry.nonempty_symplecticFraming_graphTorus hσ.isNondegenerate hh hE
  exact ⟨Φ.transDiffeomorph (diffeomorph I L) (isSymplectic_symplecticForm I L hσ).isNondegenerate
    (mpullback_diffeomorph_symplecticForm I L σ) (finrank_complex_eq_finrank_sub L hE)⟩

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
        (ProdTorusOnModel.hasSymplecticTangentImages_graphTorus (𝓡 2) L hσ hh)
        (ProdTorusOnModel.finrank_complex_eq_finrank_sub L finrank_euclideanSpace_fin)) := by
  obtain ⟨σ, hσ⟩ := ClosedSurface.exists_isSymplectic g
  exact ⟨σ, hσ, ProdTorusOnModel.nonempty_symplecticFraming_graphTorus _ _ hσ hh
    finrank_euclideanSpace_fin⟩

end ClosedSurface

end SymplecticGeometry

end

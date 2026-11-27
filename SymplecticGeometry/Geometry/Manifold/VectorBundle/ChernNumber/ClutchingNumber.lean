/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.CubeToSphere
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ChernNumber.Clutching
import SymplecticGeometry.Topology.Circle.Degree.Square
import SymplecticGeometry.Topology.Homotopy.Cube.Radius
import SymplecticGeometry.Topology.VectorBundle.Complex.Clutching
import SymplecticGeometry.Topology.VectorBundle.Pullback

/-!
# Clutching numbers and first Chern numbers

Let `p : Ω^ (Fin 2) X x` be a based sphere, a map from the square `I²` sending its boundary to
`x`, and let `E` be a complex vector bundle over `X` with finite-dimensional model `G`. The map
`GenLoop.toSphere p : S² → X` that `p` induces through Tau Ceti's collapse
`TauCeti.cubeToSphere 2 : I² → S²` pulls `E` back to a bundle `E'` over `S²`. This file builds
frames of `E'` over the closed disc of the coordinate disc `CoordinateDisc.cubeToSphere` and over
the complement of its open disc, in the sense of the disc clutching formula of
`Geometry/Manifold/VectorBundle/ChernNumber/Clutching.lean`, and shows that the degree of the
normalized determinant of their clutching transition is Tau Ceti's clutching number
`TauCeti.clutchingNumber G E p` (`exists_clutchingNumber_eq_degree_clutchingTransition`).
With the disc clutching formula `chernNumber_eq_sum_degree_clutching`, for a single disc, this
identifies the clutching number with the first Chern number of `E'` for the orientation
`cubeToSphereOrientation` of `S²` (`clutchingNumber_eq_chernNumber`).

## Construction

Choose a continuous frame `ψ` of `E` along `p` (`TauCeti.exists_continuous_frame`) and the
trivialization `e` of `E` at `x`. Both frames of `E'` are frames along `p` on a closed part of the
square, read on `S²` through the collapse:

* over the closed disc, which is the image of the points of the square at distance at most `1/5`
  from the centre (`CoordinateDisc.disc_cubeToSphere`), the frame `ψ`;
* over the complement of the open disc, the image of the closed annulus `A` of the points at
  distance at least `1/5` from the centre, the frame `ψ y ∘ T (ρ y)⁻¹`. Here `ρ y` is Tau Ceti's
  radial projection `TauCeti.cubeScale (TauCeti.cubeRadius y)⁻¹ y` of the annulus onto the
  boundary of the square, and `T = e.frameTransition ψ` is the frame `ψ` read in `e`
  (`Bundle.Trivialization.frameTransition`). On the boundary `ρ` is the identity, so this frame
  is the frame `e⁻¹` at `x` there, and it descends through the collapse, which identifies the
  boundary to the north pole.

A frame along `p` on a closed set `S` of the square that agrees at points the collapse identifies
gives a frame of `E'` on the image of `S`, continuous because the collapse restricted to the
compact `S` is a quotient map onto its image, and so is its product with the locally compact
`G` (`Topology.IsQuotientMap.continuous_lift_prod_left`).

On the boundary circle of the disc, the image of the circle of radius `1/5` about the centre of
the square (`CoordinateDisc.cubeToSphere_eq_of_squareCenterOffset_eq`), the clutching transition
is `T (ρ y)⁻¹`, whose normalized determinant is Tau Ceti's clutching function
`TauCeti.clutchingFunction p ψ e` at `ρ y`. That function of `y` is continuous on the annulus and
equals the clutching function on the boundary of the square. So the degree of the loop is its
degree around the boundary of the square (`TauCeti.squareBoundaryDegree_eq_degree_toBasedLoop`),
which is the clutching number (`TauCeti.clutchingNumber_eq_squareBoundaryDegree`).

## Main results

* `SymplecticGeometry.Bundle.exists_clutchingNumber_eq_degree_clutchingTransition`: frames of the
  pull-back of `E` to `S²` over the closed disc of `CoordinateDisc.cubeToSphere` and over the
  complement of its open disc, whose clutching transition has degree the clutching number of
  `E` on `p`.
* `SymplecticGeometry.Bundle.clutchingNumber_eq_chernNumber`: the clutching number of `E` on `p`
  is the first Chern number of the pull-back of `E` to `S²`, oriented by
  `cubeToSphereOrientation`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7
  (the first Chern number of a bundle over a surface from trivializations over a disc and over
  its complement).
* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (Chern classes of complex vector bundles, and clutching).
-/

public section

noncomputable section

open Bundle Set Topology TauCeti

open scoped unitInterval Topology.Homotopy

/-- The unit sphere of `ℝ³`. -/
local notation "𝕊²" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) (1 : ℝ)

namespace SymplecticGeometry

namespace Bundle

variable {X : Type*} {x : X}
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]

/-! ### Frames along the square read on the sphere -/

variable [TopologicalSpace X]

section Descend

variable (p : Ω^ (Fin 2) X x) {S : Set (I^(Fin 2))}
  {T : Set (𝕊²)}
  (hST : TauCeti.cubeToSphere 2 '' S = T)

include hST in
private theorem exists_mem_cubeToSphere_eq (s : T) :
    ∃ y ∈ S, TauCeti.cubeToSphere 2 y = s :=
  (Set.ext_iff.1 hST s).2 s.property

private theorem apply_eq_toSphere {y : I^(Fin 2)} {s : 𝕊²}
    (h : TauCeti.cubeToSphere 2 y = s) : p y = GenLoop.toSphere p (s : 𝕊²) := by
  rw [← h, GenLoop.toSphere_cubeToSphere]

/-- A frame `χ` along `p`, read at a point `s` of the image `T` of `S` under the collapse through
a chosen preimage of `s` in `S`, as a frame of the pull-back of `E` to the sphere. -/
private def descendFrame (χ : ∀ y, G ≃L[ℂ] E (p y)) (s : T) :
    G ≃L[ℂ] (⇑(GenLoop.toSphere p) *ᵖ E) (s : 𝕊²) :=
  Pullback.castEquiv _ (apply_eq_toSphere p (exists_mem_cubeToSphere_eq hST s).choose_spec.2)
    (χ (exists_mem_cubeToSphere_eq hST s).choose)

private theorem castEquiv_congr (χ : ∀ y, G ≃L[ℂ] E (p y)) {y y' : I^(Fin 2)}
    {s : 𝕊²} (hy : y = y')
    (h : p y = GenLoop.toSphere p (s : 𝕊²)) (h' : p y' = GenLoop.toSphere p (s : 𝕊²)) :
    Pullback.castEquiv _ h (χ y) = Pullback.castEquiv _ h' (χ y') := by
  subst hy
  rfl

/-- At a point of `T` that is the image of a point `y` of `S` off the boundary of the square, the
descended frame is `χ y`. -/
private theorem descendFrame_eq (χ : ∀ y, G ≃L[ℂ] E (p y)) (s : T) {y : I^(Fin 2)}
    (hys : TauCeti.cubeToSphere 2 y = s) (hy : y ∉ Cube.boundary (Fin 2)) :
    descendFrame p hST χ s = Pullback.castEquiv _ (apply_eq_toSphere p hys) (χ y) := by
  obtain ⟨-, h₀⟩ := (exists_mem_cubeToSphere_eq hST s).choose_spec
  refine castEquiv_congr p χ ?_ _ _
  rcases cubeToSphere_eq_cubeToSphere_iff.1 (h₀.trans hys.symm) with h | ⟨-, h⟩
  · exact h
  · exact absurd h hy

variable {p} {χ : ∀ y, G ≃L[ℂ] E (p y)}
  (hcompat : ∀ y ∈ S, ∀ y' ∈ S, TauCeti.cubeToSphere 2 y = TauCeti.cubeToSphere 2 y' →
    ∀ v, TotalSpace.mk' G (p y) (χ y v) = TotalSpace.mk' G (p y') (χ y' v))

include hcompat in
private theorem mk_descendFrame (s : T) {y : I^(Fin 2)} (hy : y ∈ S)
    (hys : TauCeti.cubeToSphere 2 y = s) (v : G) :
    Pullback.lift (GenLoop.toSphere p) (TotalSpace.mk' G (s : 𝕊²) (descendFrame p hST χ s v)) =
      TotalSpace.mk' G (p y) (χ y v) := by
  obtain ⟨h₀S, h₀⟩ := (exists_mem_cubeToSphere_eq hST s).choose_spec
  rw [descendFrame, Pullback.lift_mk_castEquiv]
  exact hcompat _ h₀S _ hy (h₀.trans hys.symm) v

variable [TopologicalSpace (TotalSpace G E)] [FiniteDimensional ℂ G]

include hcompat in
/-- The descended frame of a frame along `p` continuous on the closed set `S` is a continuous
frame of the pull-back of `E` to the sphere over `T`. -/
private theorem continuous_descendFrame (hS : IsClosed S)
    (hχ : ContinuousOn (fun q : (Fin 2 → I) × G ↦ TotalSpace.mk' G (p q.1) (χ q.1 q.2))
      (S ×ˢ univ)) :
    Continuous fun q : T × G ↦ TotalSpace.mk' G (E := ⇑(GenLoop.toSphere p) *ᵖ E) (q.1 : 𝕊²)
      (descendFrame p hST χ q.1 q.2) := by
  let k : S → T := fun y ↦ ⟨TauCeti.cubeToSphere 2 y, hST ▸ mem_image_of_mem _ y.property⟩
  have hk : Continuous k := (((TauCeti.cubeToSphere 2).continuous.comp
    continuous_subtypeVal).subtype_mk _)
  have : CompactSpace S := isCompact_iff_compactSpace.1 hS.isCompact
  have hq : IsQuotientMap k := hk.isClosedMap.isQuotientMap hk fun s ↦ by
    obtain ⟨y, hy, hys⟩ := exists_mem_cubeToSphere_eq hST s
    exact ⟨⟨y, hy⟩, Subtype.ext hys⟩
  refine hq.continuous_lift_prod_left (Pullback.continuous_iff.2 ⟨?_, ?_⟩)
  · exact (TauCeti.cubeToSphere 2).continuous.comp (continuous_subtypeVal.comp continuous_fst)
  · have heq : (fun q : S × G ↦ Pullback.lift (GenLoop.toSphere p)
        (TotalSpace.mk' G (k q.1 : 𝕊²) (descendFrame p hST χ (k q.1) q.2))) =
        fun q : S × G ↦ TotalSpace.mk' G (p q.1) (χ q.1 q.2) :=
      funext fun q ↦ mk_descendFrame hST hcompat (k q.1) q.1.property rfl q.2
    rw [heq]
    exact hχ.comp_continuous ((continuous_subtypeVal.comp continuous_fst).prodMk continuous_snd)
      fun q ↦ ⟨q.1.property, mem_univ _⟩

end Descend

/-! ### The frames and their clutching transition -/

section Frames

/-- The points of the square at distance at most `1/5` from the centre. -/
private def innerDisc : Set (I^(Fin 2)) :=
  {y | ‖squareCenterOffset y‖ ≤ 1 / 5}

/-- The points of the square at distance at least `1/5` from the centre. -/
private def outerAnnulus : Set (I^(Fin 2)) :=
  {y | 1 / 5 ≤ ‖squareCenterOffset y‖}

private theorem isClosed_innerDisc : IsClosed innerDisc :=
  isClosed_le continuous_squareCenterOffset.norm continuous_const

private theorem isClosed_outerAnnulus : IsClosed outerAnnulus :=
  isClosed_le continuous_const continuous_squareCenterOffset.norm

private theorem notMem_boundary_of_mem_innerDisc {y : I^(Fin 2)} (hy : y ∈ innerDisc) :
    y ∉ Cube.boundary (Fin 2) := fun hb ↦ by
  simp only [innerDisc, mem_ofPred_eq] at hy
  linarith [one_half_le_norm_squareCenterOffset_of_mem hb]

/-- The annulus avoids the centre of the square, where the radius vanishes. -/
private theorem cubeRadius_ne_zero_of_mem_outerAnnulus {y : I^(Fin 2)} (hy : y ∈ outerAnnulus) :
    cubeRadius y ≠ 0 := fun h ↦ by
  rw [cubeRadius_eq_zero_iff] at h
  subst h
  simp only [outerAnnulus, mem_ofPred_eq, squareCenterOffset_cubeCenter, norm_zero] at hy
  norm_num at hy

/-- The radial projection of the annulus onto the boundary of the square lands in the
boundary. -/
private theorem cubeScale_mem_boundary_of_mem_outerAnnulus {y : I^(Fin 2)}
    (hy : y ∈ outerAnnulus) : cubeScale (cubeRadius y)⁻¹ y ∈ Cube.boundary (Fin 2) :=
  cubeScale_inv_cubeRadius_mem_boundary (cubeRadius_ne_zero_of_mem_outerAnnulus hy)

/-- The radial projection of the annulus onto the boundary of the square is continuous. -/
private theorem continuousOn_cubeScale_outerAnnulus :
    ContinuousOn (fun y : I^(Fin 2) ↦ cubeScale (cubeRadius y)⁻¹ y) outerAnnulus :=
  continuousOn_cubeScale_inv_cubeRadius.mono fun _ ↦ cubeRadius_ne_zero_of_mem_outerAnnulus

/-- The points with offset `ζ / 5` from the centre, for `ζ` on the unit circle, lie in the
annulus and off the boundary of the square. -/
private theorem mem_outerAnnulus_of_squareCenterOffset_eq {ζ : Circle} {y : I^(Fin 2)}
    (hy : squareCenterOffset y = ((1 / 5 : ℝ) : ℂ) * ζ) :
    y ∈ outerAnnulus ∧ y ∉ Cube.boundary (Fin 2) := by
  have hnorm : ‖squareCenterOffset y‖ = 1 / 5 := by
    rw [hy, norm_mul, Circle.norm_coe, mul_one]
    norm_num
  refine ⟨hnorm.symm.le, fun hb ↦ ?_⟩
  linarith [one_half_le_norm_squareCenterOffset_of_mem hb]

private theorem image_innerDisc :
    TauCeti.cubeToSphere 2 '' innerDisc = CoordinateDisc.cubeToSphere.disc := by
  rw [CoordinateDisc.disc_cubeToSphere, innerDisc]

private theorem image_outerAnnulus :
    TauCeti.cubeToSphere 2 '' outerAnnulus =
      discComplement (fun _ : Unit ↦ CoordinateDisc.cubeToSphere) := by
  ext s
  rw [mem_discComplement_iff, CoordinateDisc.openDisc_cubeToSphere]
  constructor
  · rintro ⟨y, hy, rfl⟩ - ⟨y', hy', h⟩
    rw [mem_ofPred_eq] at hy'
    rcases cubeToSphere_eq_cubeToSphere_iff.1 h with rfl | ⟨hb, -⟩
    · exact (not_le.2 hy') hy
    · linarith [one_half_le_norm_squareCenterOffset_of_mem hb]
  · intro h
    obtain ⟨y, rfl⟩ := cubeToSphere_surjective 2 s
    refine ⟨y, ?_, rfl⟩
    rw [outerAnnulus, mem_ofPred_eq, ← not_lt]
    exact fun hy ↦ h () ⟨y, hy, rfl⟩

variable [TopologicalSpace (TotalSpace G E)] [FiberBundle G E] [VectorBundle ℂ G E]
  {p : Ω^ (Fin 2) X x} {ψ : ∀ y, G ≃L[ℂ] E (p y)}
  (hψ : Continuous fun q : (Fin 2 → I) × G ↦ TotalSpace.mk' G (p q.1) (ψ q.1 q.2))

/-- The frame over the annulus: `ψ y` composed with the inverse of the transition of `ψ` in the
trivialization at `x`, taken at the radial projection of `y` onto the boundary of the square. -/
private def annulusFrame (ψ : ∀ y, G ≃L[ℂ] E (p y)) (y : I^(Fin 2)) : G ≃L[ℂ] E (p y) :=
  ((trivializationAt G E x).frameTransition ψ (cubeScale (cubeRadius y)⁻¹ y)).symm.trans (ψ y)

omit [NormedSpace ℂ G] [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [VectorBundle ℂ G E] in
private theorem apply_cubeScale_mem {y : I^(Fin 2)} (hy : y ∈ outerAnnulus) :
    p (cubeScale (cubeRadius y)⁻¹ y) ∈ (trivializationAt G E x).baseSet := by
  rw [GenLoop.boundary p _ (cubeScale_mem_boundary_of_mem_outerAnnulus hy)]
  exact mem_baseSet_trivializationAt G E x

include hψ in
private theorem continuousOn_annulusFrame [FiniteDimensional ℂ G] :
    ContinuousOn (fun q : (Fin 2 → I) × G ↦ TotalSpace.mk' G (p q.1) (annulusFrame ψ q.1 q.2))
      (outerAnnulus ×ˢ univ) := by
  have hT : ContinuousOn (fun y ↦ (((trivializationAt G E x).frameTransition ψ
      (cubeScale (cubeRadius y)⁻¹ y)).symm : G →L[ℂ] G)) outerAnnulus :=
    (Trivialization.continuousOn_frameTransition_symm hψ _).comp
      continuousOn_cubeScale_outerAnnulus fun y hy ↦ apply_cubeScale_mem hy
  exact hψ.comp_continuousOn (continuousOn_fst.prodMk
    ((hT.comp continuousOn_fst fun q (hq : q ∈ outerAnnulus ×ˢ univ) ↦ hq.1).clm_apply
      continuousOn_snd))

/-- On the boundary of the square the annulus frame is the frame of the trivialization at `x`. -/
private theorem mk_annulusFrame_of_mem {y : I^(Fin 2)} (hy : y ∈ Cube.boundary (Fin 2)) (v : G) :
    TotalSpace.mk' G (p y) (annulusFrame ψ y v) =
      TotalSpace.mk' G x ((trivializationAt G E x).symm x v) := by
  have hb : p y ∈ (trivializationAt G E x).baseSet :=
    by rw [GenLoop.boundary p y hy]; exact mem_baseSet_trivializationAt G E x
  have h : annulusFrame ψ y v = (trivializationAt G E x).symm (p y) v := by
    rw [annulusFrame, (cubeRadius_eq_one_iff y).2 hy, inv_one, cubeScale_one,
      Trivialization.frameTransition_of_mem hb]
    simp [Trivialization.continuousLinearEquivAt_symm_apply]
  rw [h, GenLoop.boundary p y hy]

omit [TopologicalSpace (TotalSpace G E)] [FiberBundle G E] [VectorBundle ℂ G E] in
/-- The frame `ψ` agrees with itself at the points of the inner disc that the collapse
identifies, since it identifies none. -/
private theorem mk_eq_mk_of_mem_innerDisc :
    ∀ y ∈ innerDisc, ∀ y' ∈ innerDisc, TauCeti.cubeToSphere 2 y = TauCeti.cubeToSphere 2 y' →
      ∀ v, TotalSpace.mk' G (p y) (ψ y v) = TotalSpace.mk' G (p y') (ψ y' v) := by
  intro y hy y' _ h v
  rcases cubeToSphere_eq_cubeToSphere_iff.1 h with rfl | ⟨hb, -⟩
  · rfl
  · exact absurd hb (notMem_boundary_of_mem_innerDisc hy)

/-- The annulus frame agrees at the points of the annulus that the collapse identifies. -/
private theorem mk_annulusFrame_eq_of_mem_outerAnnulus :
    ∀ y ∈ outerAnnulus, ∀ y' ∈ outerAnnulus,
      TauCeti.cubeToSphere 2 y = TauCeti.cubeToSphere 2 y' → ∀ v,
        TotalSpace.mk' G (p y) (annulusFrame ψ y v) =
          TotalSpace.mk' G (p y') (annulusFrame ψ y' v) := by
  intro y _ y' _ h v
  rcases cubeToSphere_eq_cubeToSphere_iff.1 h with rfl | ⟨hb, hb'⟩
  · rfl
  · rw [mk_annulusFrame_of_mem hb, mk_annulusFrame_of_mem hb']

/-- On the boundary circle of the disc, at the image of the point `y` with offset `ζ / 5`, the
clutching transition of the two descended frames is the inverse of the transition of `ψ` in the
trivialization at `x`, taken at the radial projection of `y`. -/
private theorem clutchingTransition_descendFrame {ζ : Circle} {y : I^(Fin 2)}
    (hy : squareCenterOffset y = ((1 / 5 : ℝ) : ℂ) * ζ) :
    clutchingTransition (φ := fun _ : Unit ↦ CoordinateDisc.cubeToSphere) Subsingleton.pairwise
        (fun _ ↦ descendFrame p image_innerDisc ψ)
        (descendFrame p image_outerAnnulus (annulusFrame ψ)) () ζ =
      ((trivializationAt G E x).frameTransition ψ (cubeScale (cubeRadius y)⁻¹ y)).symm := by
  have hyb := (mem_outerAnnulus_of_squareCenterOffset_eq hy).2
  have hys : TauCeti.cubeToSphere 2 y = CoordinateDisc.cubeToSphere.boundaryCircle ζ := by
    rw [CoordinateDisc.boundaryCircle_apply]
    exact (CoordinateDisc.cubeToSphere_eq_of_squareCenterOffset_eq _ hy).symm
  rw [clutchingTransition_def, descendFrame_eq _ _ _ _ hys hyb, descendFrame_eq _ _ _ _ hys hyb,
    Pullback.castEquiv_trans_symm]
  ext v
  simp [annulusFrame]

/-- **Clutching frames of a bundle pulled back to the sphere.** Let `p : I² → X` be a sphere based
at `x` and `E` a complex vector bundle over `X` with finite-dimensional model `G`. The pull-back
of `E` to `S²` along the map `GenLoop.toSphere p` induced by `p` has a continuous frame `Φ` over
the closed disc of the coordinate disc `CoordinateDisc.cubeToSphere` and a continuous frame
`Φout` over the complement of its open disc, such that the degree of the normalized determinant
of the clutching transition `(Φ)⁻¹ ∘ Φout` around the boundary circle is the clutching number
`TauCeti.clutchingNumber G E p`. -/
theorem exists_clutchingNumber_eq_degree_clutchingTransition [FiniteDimensional ℂ G]
    [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)] (p : Ω^ (Fin 2) X x) :
    ∃ (Φ : ∀ (_ : Unit) (s : CoordinateDisc.cubeToSphere.disc),
        G ≃L[ℂ] (⇑(GenLoop.toSphere p) *ᵖ E) (s : 𝕊²))
      (Φout : ∀ s : discComplement (fun _ : Unit ↦ CoordinateDisc.cubeToSphere),
        G ≃L[ℂ] (⇑(GenLoop.toSphere p) *ᵖ E) (s : 𝕊²))
      (hΦ : ∀ i, Continuous fun q : CoordinateDisc.cubeToSphere.disc × G ↦
        TotalSpace.mk' G (E := ⇑(GenLoop.toSphere p) *ᵖ E) (q.1 : 𝕊²) (Φ i q.1 q.2))
      (hΦout : Continuous fun q : discComplement (fun _ : Unit ↦ CoordinateDisc.cubeToSphere) × G ↦
        TotalSpace.mk' G (E := ⇑(GenLoop.toSphere p) *ᵖ E) (q.1 : 𝕊²) (Φout q.1 q.2)),
      clutchingNumber G E p = Circle.degree (ContinuousMap.mk _
        (continuous_normalizedDet_clutchingTransition
          (φ := fun _ : Unit ↦ CoordinateDisc.cubeToSphere) Subsingleton.pairwise hΦ hΦout
          ())).toBasedLoop := by
  have : CompleteSpace G := FiniteDimensional.completeSpace ℂ G
  obtain ⟨ψ, hψ⟩ := exists_continuous_frame (𝕜 := ℂ) (F := G) (E := E) (map_continuous p)
  set e := trivializationAt G E x
  refine ⟨fun _ ↦ descendFrame p image_innerDisc ψ,
    descendFrame p image_outerAnnulus (annulusFrame ψ),
    fun _ ↦ continuous_descendFrame image_innerDisc mk_eq_mk_of_mem_innerDisc isClosed_innerDisc
      hψ.continuousOn,
    continuous_descendFrame image_outerAnnulus mk_annulusFrame_eq_of_mem_outerAnnulus
      isClosed_outerAnnulus (continuousOn_annulusFrame hψ), ?_⟩
  -- The clutching function, read at the radial projection onto the boundary of the square.
  let Γ : (Fin 2 → I) → Circle := fun y ↦ clutchingFunction p ψ e (cubeScale (cubeRadius y)⁻¹ y)
  have hΓ : ContinuousOn Γ outerAnnulus :=
    (continuousOn_clutchingFunction hψ e).comp continuousOn_cubeScale_outerAnnulus
      fun y hy ↦ apply_cubeScale_mem hy
  have hb : EqOn (clutchingFunction p ψ e) Γ (Cube.boundary (Fin 2)) := fun y hy ↦ by
    simp only [Γ, (cubeRadius_eq_one_iff y).2 hy, inv_one, cubeScale_one]
  rw [clutchingNumber_eq_squareBoundaryDegree p e (mem_baseSet_trivializationAt G E x) hψ,
    squareBoundaryDegree_congr hb]
  refine squareBoundaryDegree_eq_degree_toBasedLoop (by norm_num) (by norm_num) hΓ _
    fun ζ y hy ↦ ?_
  rw [ContinuousMap.coe_mk, clutchingTransition_descendFrame hy,
    ContinuousLinearEquiv.normalizedDet_symm, Trivialization.normalizedDet_frameTransition_inv
      (apply_cubeScale_mem (mem_outerAnnulus_of_squareCenterOffset_eq hy).1)]

/-- **Clutching numbers are first Chern numbers.** Let `p : I² → X` be a sphere based at `x` and
`E` a complex vector bundle over `X` with finite-dimensional model `G`. Tau Ceti's clutching
number `TauCeti.clutchingNumber G E p` is the first Chern number of the pull-back of `E` to `S²`
along the map `GenLoop.toSphere p` induced by `p`, for the orientation `cubeToSphereOrientation`
of `S²`, for which the collapse of the square preserves orientation on the open square. -/
theorem clutchingNumber_eq_chernNumber {E : X → Type} [∀ x, AddCommGroup (E x)]
    [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace G E)]
    [FiberBundle G E] [VectorBundle ℂ G E] [FiniteDimensional ℂ G]
    [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)] (p : Ω^ (Fin 2) X x) :
    clutchingNumber G E p = chernNumber cubeToSphereOrientation finrank_euclideanSpace_fin G
      (⇑(GenLoop.toSphere p) *ᵖ E) := by
  obtain ⟨Φ, Φout, hΦ, hΦout, h⟩ :=
    exists_clutchingNumber_eq_degree_clutchingTransition (G := G) (E := E) p
  rw [h, chernNumber_eq_sum_degree_clutching Subsingleton.pairwise hΦ hΦout,
    Fintype.sum_unique]

end Frames

end Bundle

end SymplecticGeometry

end

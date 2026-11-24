/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.RealAlgebraic.Semialgebraic.OneVariable
public import SymplecticGeometry.Order.Interval.Set.IsoIoo

/-!
# Semialgebraic choice

A semialgebraic family of subsets of `ℝ`, given as a semialgebraic set
`S : Set (σ ⊕ Unit → ℝ)` whose fiber over `x : σ → ℝ` is `{t | Sum.elim x (fun _ ↦ t) ∈ S}`, has a
semialgebraic section: a function `f`, semialgebraic on the set of parameters with nonempty fiber,
with `Sum.elim x (f x) ∈ S` there. This is definable choice for one coordinate; by induction on
the number of coordinates it extends to a semialgebraic family `S : Set (σ ⊕ τ → ℝ)` of subsets
of `τ → ℝ` for any finite `τ`.

* `TauCeti.IsSemialgebraic.exists_isSemialgebraicOn_sumElim_mem_unit`: semialgebraic choice for
  one output coordinate. The parameters `σ` need not be finite.
* `TauCeti.IsSemialgebraic.exists_isSemialgebraicOn_sumElim_mem`: semialgebraic choice for
  finitely many output coordinates `τ`. Again `σ` need not be finite.

On the way, the file proves tools for showing that a set described by a formula is semialgebraic:

* `TauCeti.IsSemialgebraic.setOf_sumElim_mem`: the fibers of a semialgebraic set are
  semialgebraic.
* `TauCeti.isSemialgebraic_setOf_apply_lt`: the set where one coordinate is less than another.
* `TauCeti.IsSemialgebraic.setOf_exists_scalar`, `TauCeti.IsSemialgebraic.setOf_forall_scalar`:
  a quantifier over one more coordinate.
* `TauCeti.isSemialgebraicOn_of_setOf_iff`: a function is semialgebraic on `D` if a
  semialgebraic relation cuts out its graph over `D`.
* `TauCeti.isSemialgebraic_setOf_mul_one_add_abs_eq` and
  `TauCeti.isSemialgebraicOn_div_one_sub_abs`: over an ordered field `R`, the
  bijection `t ↦ t / (1 + |t|)` of `R` onto `(-1, 1)` has a semialgebraic graph, and its inverse
  `u ↦ u / (1 - |u|)` is semialgebraic. The graph is described by `mul_one_add_abs_eq_iff`.

## Proof

First assume that every fiber lies in `(-1, 1)`. Let `a` be the infimum of a nonempty fiber. If
`a` lies in the fiber, choose `a`. Otherwise the fiber contains every point just right of `a`
(`TauCeti.IsSemialgebraic.eventually_nhdsGT_mem_or_notMem`), hence an interval `(a, b)` that no
longer interval `(a, c)` extends, and we choose its midpoint. Both alternatives are expressed by
one first-order formula in the coordinates, with quantifiers over single real numbers, which
determines the chosen point; so the graph of the choice is semialgebraic, by
`TauCeti.IsSemialgebraic.setOf_exists_sumElim` and `TauCeti.IsSemialgebraic.setOf_forall_sumElim`
for the quantifiers and `TauCeti.IsSemialgebraic.preimage_comp` for the changes of coordinates.
In general, the homeomorphism `t ↦ t / (1 + |t|)` moves the fibers into `(-1, 1)`, and composing
the choice there with the inverse `u ↦ u / (1 - |u|)` (`TauCeti.IsSemialgebraicOn.comp`) brings
the chosen point back.

For finitely many output coordinates we induct on `τ` (`Finite.induction_empty_option`),
transporting the statement along bijections of `τ`
(`TauCeti.isSemialgebraicOn_comp_equiv_iff`). With no output coordinates the section is constant.
For `α ⊕ Unit`, regroup the coordinates of `S` as `(σ ⊕ α) ⊕ Unit` and let `T ⊆ (σ ⊕ α → ℝ)`
be its projection forgetting the last coordinate. Choose `f₁` for `T` by induction, and `g`
for the last coordinate over `T` by the one-coordinate result; then
`x ↦ Sum.elim (f₁ x) (g (Sum.elim x (f₁ x)))` is a section. Its graph is the intersection of
preimages of the graphs of `f₁` and `g` under changes of coordinates, so no projection, and no
finiteness of `σ`, is needed to see that it is semialgebraic.

## References

* L. van den Dries, *Tame Topology and o-minimal Structures*, Cambridge University Press, 1998,
  Chapter 6, Section 1.
* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998, Sections 2.3–2.4.
-/

public section

open Set Topology MvPolynomial

namespace TauCeti

variable {σ τ R : Type*}

/-! ### Sets cut out by formulas in one more coordinate -/

section Formula

variable [CommRing R] [LinearOrder R]

private theorem isSemialgebraic_setOf_of_iff {P : (σ → R) → Prop} {s : Set (σ → R)}
    (hs : IsSemialgebraic s) (h : ∀ z, P z ↔ z ∈ s) : IsSemialgebraic {z | P z} := by
  convert hs using 1
  ext z
  exact h z

private theorem isSemialgebraic_setOf_mem_of_eq_comp {s : Set (τ → R)}
    (hs : IsSemialgebraic s) (e : τ → σ) {g : (σ → R) → τ → R} (hg : ∀ z, g z = z ∘ e) :
    IsSemialgebraic {z | g z ∈ s} :=
  isSemialgebraic_setOf_of_iff (hs.preimage_comp e) fun z ↦ by simp [hg]

private theorem isSemialgebraic_setOf_and {P Q : (σ → R) → Prop}
    (hP : IsSemialgebraic {z | P z}) (hQ : IsSemialgebraic {z | Q z}) :
    IsSemialgebraic {z | P z ∧ Q z} :=
  hP.inter hQ

private theorem isSemialgebraic_setOf_or {P Q : (σ → R) → Prop}
    (hP : IsSemialgebraic {z | P z}) (hQ : IsSemialgebraic {z | Q z}) :
    IsSemialgebraic {z | P z ∨ Q z} :=
  hP.union hQ

private theorem isSemialgebraic_setOf_not {P : (σ → R) → Prop}
    (hP : IsSemialgebraic {z | P z}) : IsSemialgebraic {z | ¬ P z} :=
  hP.compl

private theorem isSemialgebraic_setOf_imp {P Q : (σ → R) → Prop}
    (hP : IsSemialgebraic {z | P z}) (hQ : IsSemialgebraic {z | Q z}) :
    IsSemialgebraic {z | P z → Q z} :=
  isSemialgebraic_setOf_of_iff (hP.compl.union hQ) fun z ↦ by
    simp [imp_iff_not_or]

/-- A fiber `{y | Sum.elim x y ∈ S}` of a semialgebraic set `S` of points `σ ⊕ τ → R` is
semialgebraic. -/
theorem IsSemialgebraic.setOf_sumElim_mem {S : Set (σ ⊕ τ → R)} (hS : IsSemialgebraic S)
    (x : σ → R) : IsSemialgebraic {y : τ → R | Sum.elim x y ∈ S} := by
  refine isSemialgebraic_setOf_of_iff
    (hS.preimage_eval (Sum.elim (fun i ↦ C (x i)) X)) fun y ↦ ?_
  rw [mem_preimage]
  convert Iff.rfl using 2
  ext (i | i) <;> simp

/-- The set of points `z : σ → R` with `z i < z j` is semialgebraic. -/
theorem isSemialgebraic_setOf_apply_lt [IsOrderedAddMonoid R] (i j : σ) :
    IsSemialgebraic {z : σ → R | z i < z j} :=
  isSemialgebraic_setOf_of_iff (isSemialgebraic_eval_lt (X i) (X j)) fun z ↦ by simp

variable [HasSemialgebraicProjections R]

/-- If a relation `P x t` between `x : σ → R` and one more coordinate `t : R` cuts out a
semialgebraic subset of `σ ⊕ Unit → R`, then `{x | ∃ t, P x t}` is semialgebraic. -/
theorem IsSemialgebraic.setOf_exists_scalar {P : (σ → R) → R → Prop}
    (h : IsSemialgebraic {z : σ ⊕ Unit → R | P (z ∘ Sum.inl) (z (Sum.inr ()))}) :
    IsSemialgebraic {x : σ → R | ∃ t, P x t} :=
  isSemialgebraic_setOf_of_iff h.setOf_exists_sumElim fun x ↦ by
    simp only [mem_ofPred_eq, Sum.elim_comp_inl, Sum.elim_inr]
    exact ⟨fun ⟨t, ht⟩ ↦ ⟨fun _ ↦ t, ht⟩, fun ⟨y, hy⟩ ↦ ⟨y (), hy⟩⟩

/-- If a relation `P x t` between `x : σ → R` and one more coordinate `t : R` cuts out a
semialgebraic subset of `σ ⊕ Unit → R`, then `{x | ∀ t, P x t}` is semialgebraic. -/
theorem IsSemialgebraic.setOf_forall_scalar {P : (σ → R) → R → Prop}
    (h : IsSemialgebraic {z : σ ⊕ Unit → R | P (z ∘ Sum.inl) (z (Sum.inr ()))}) :
    IsSemialgebraic {x : σ → R | ∀ t, P x t} :=
  isSemialgebraic_setOf_of_iff h.setOf_forall_sumElim fun x ↦ by
    simp only [mem_ofPred_eq, Sum.elim_comp_inl, Sum.elim_inr]
    exact ⟨fun h y ↦ h (y ()), fun h t ↦ h fun _ ↦ t⟩

/-- A function `f : (σ → R) → (τ → R)`, `τ` finite, is semialgebraic on `D` if a relation `G`,
which holds for `x` and `y` exactly when `x ∈ D` and `y = f x`, cuts out a semialgebraic subset
of `σ ⊕ τ → R`. -/
theorem isSemialgebraicOn_of_setOf_iff [Finite τ] {D : Set (σ → R)} {f : (σ → R) → τ → R}
    {G : (σ → R) → (τ → R) → Prop}
    (hG : IsSemialgebraic {z : σ ⊕ τ → R | G (z ∘ Sum.inl) (z ∘ Sum.inr)})
    (h : ∀ x y, G x y ↔ x ∈ D ∧ f x = y) : IsSemialgebraicOn f D :=
  isSemialgebraicOn_iff_graph.2 (isSemialgebraic_setOf_of_iff hG fun _ ↦
    mem_preimage_sumArrowEquivProdArrow_graphOn.trans (h _ _).symm)

end Formula

/-- The formula that picks a point `t` of the fiber `{t | Sum.elim x (fun _ ↦ t) ∈ S}`: `t` is its
least point, or the fiber has no point at or below some `a`, contains `(a, b)`, contains no longer
interval `(a, c)`, and `t` is the midpoint of `(a, b)`. -/
private def ChoicePred (S : Set (σ ⊕ Unit → ℝ)) (x : σ → ℝ) (t : ℝ) : Prop :=
  (Sum.elim x (fun _ ↦ t) ∈ S ∧ ∀ s, s < t → Sum.elim x (fun _ ↦ s) ∉ S) ∨
    ∃ a, ∃ b, a < b ∧ 2 * t = a + b ∧ (∀ s, s < a → Sum.elim x (fun _ ↦ s) ∉ S) ∧
      Sum.elim x (fun _ ↦ a) ∉ S ∧ (∀ s, a < s → s < b → Sum.elim x (fun _ ↦ s) ∈ S) ∧
      ∀ c, b < c → ∃ s, a < s ∧ s < c ∧ Sum.elim x (fun _ ↦ s) ∉ S

private theorem isSemialgebraic_choicePred {S : Set (σ ⊕ Unit → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic {z : σ ⊕ Unit → ℝ | ChoicePred S (z ∘ Sum.inl) (z (Sum.inr ()))} := by
  unfold ChoicePred
  refine isSemialgebraic_setOf_or (isSemialgebraic_setOf_and ?_ ?_) ?_
  · exact isSemialgebraic_setOf_mem_of_eq_comp hS id fun z ↦ by ext (i | i) <;> rfl
  · refine IsSemialgebraic.setOf_forall_scalar (isSemialgebraic_setOf_imp ?_ ?_)
    · exact isSemialgebraic_setOf_apply_lt _ _
    · exact isSemialgebraic_setOf_not (isSemialgebraic_setOf_mem_of_eq_comp hS
        (Sum.elim (Sum.inl ∘ Sum.inl) fun _ ↦ Sum.inr ()) fun z ↦ by ext (i | i) <;> rfl)
  · refine IsSemialgebraic.setOf_exists_scalar (IsSemialgebraic.setOf_exists_scalar ?_)
    refine isSemialgebraic_setOf_and ?_ (isSemialgebraic_setOf_and ?_
      (isSemialgebraic_setOf_and ?_ (isSemialgebraic_setOf_and ?_
        (isSemialgebraic_setOf_and ?_ ?_))))
    · exact isSemialgebraic_setOf_apply_lt (Sum.inl (Sum.inr ())) (Sum.inr ())
    · exact isSemialgebraic_setOf_of_iff
        (isSemialgebraic_eval_eq (2 * X (Sum.inl (Sum.inl (Sum.inr ()))))
          (X (Sum.inl (Sum.inr ())) + X (Sum.inr ()))) fun z ↦ by simp
    · refine IsSemialgebraic.setOf_forall_scalar (isSemialgebraic_setOf_imp ?_ ?_)
      · exact isSemialgebraic_setOf_apply_lt (Sum.inr ()) (Sum.inl (Sum.inl (Sum.inr ())))
      · exact isSemialgebraic_setOf_not (isSemialgebraic_setOf_mem_of_eq_comp hS
          (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ Sum.inl) fun _ ↦ Sum.inr ())
          fun z ↦ by ext (i | i) <;> rfl)
    · exact isSemialgebraic_setOf_not (isSemialgebraic_setOf_mem_of_eq_comp hS
        (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl) fun _ ↦ Sum.inl (Sum.inr ()))
        fun z ↦ by ext (i | i) <;> rfl)
    · refine IsSemialgebraic.setOf_forall_scalar (isSemialgebraic_setOf_imp ?_
        (isSemialgebraic_setOf_imp ?_ ?_))
      · exact isSemialgebraic_setOf_apply_lt (Sum.inl (Sum.inl (Sum.inr ()))) (Sum.inr ())
      · exact isSemialgebraic_setOf_apply_lt (Sum.inr ()) (Sum.inl (Sum.inr ()))
      · exact isSemialgebraic_setOf_mem_of_eq_comp hS
          (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ Sum.inl) fun _ ↦ Sum.inr ())
          fun z ↦ by ext (i | i) <;> rfl
    · refine IsSemialgebraic.setOf_forall_scalar (isSemialgebraic_setOf_imp ?_
        (IsSemialgebraic.setOf_exists_scalar (isSemialgebraic_setOf_and ?_
          (isSemialgebraic_setOf_and ?_ ?_))))
      · exact isSemialgebraic_setOf_apply_lt (Sum.inl (Sum.inr ())) (Sum.inr ())
      · exact isSemialgebraic_setOf_apply_lt (Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))
          (Sum.inr ())
      · exact isSemialgebraic_setOf_apply_lt (Sum.inr ()) (Sum.inl (Sum.inr ()))
      · exact isSemialgebraic_setOf_not (isSemialgebraic_setOf_mem_of_eq_comp hS
          (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ Sum.inl) fun _ ↦ Sum.inr ())
          fun z ↦ by ext (i | i) <;> rfl)

/-- If a set `M` of reals contains a nonempty interval `(a, b)` and has no point below `a'`, then
`a' ≤ a`. -/
private theorem le_of_forall_mem_Ioo {M : ℝ → Prop} {a b a' : ℝ} (hab : a < b)
    (hM : ∀ s, a < s → s < b → M s) (ha' : ∀ s, s < a' → ¬ M s) : a' ≤ a := by
  by_contra! h
  exact ha' ((a + min a' b) / 2) (by linarith [min_le_left a' b])
    (hM _ (by linarith [lt_min h hab]) (by linarith [min_le_right a' b]))

private theorem ChoicePred.mem {S : Set (σ ⊕ Unit → ℝ)} {x : σ → ℝ} {t : ℝ}
    (h : ChoicePred S x t) : Sum.elim x (fun _ ↦ t) ∈ S := by
  obtain h | ⟨a, b, hab, ht, -, -, hM, -⟩ := h
  exacts [h.1, hM t (by linarith) (by linarith)]

private theorem ChoicePred.unique {S : Set (σ ⊕ Unit → ℝ)} {x : σ → ℝ} {t t' : ℝ}
    (h : ChoicePred S x t) (h' : ChoicePred S x t') : t = t' := by
  -- A least point of the fiber excludes an interval right of an infimum outside the fiber.
  have hmin {t a b : ℝ} (ht : Sum.elim x (fun _ ↦ t) ∈ S)
      (ht' : ∀ s, s < t → Sum.elim x (fun _ ↦ s) ∉ S) (hab : a < b)
      (ha : ∀ s, s < a → Sum.elim x (fun _ ↦ s) ∉ S) (ha' : Sum.elim x (fun _ ↦ a) ∉ S)
      (hM : ∀ s, a < s → s < b → Sum.elim x (fun _ ↦ s) ∈ S) : False := by
    have h₁ := le_of_forall_mem_Ioo hab hM ht'
    rcases h₁.lt_or_eq with h₁ | rfl
    exacts [ha t h₁ ht, ha' ht]
  obtain ⟨ht, ht'⟩ | ⟨a, b, hab, ht, ha, ha', hM, hb⟩ := h <;>
    obtain ⟨hs, hs'⟩ | ⟨a', b', hab', hs, hc, hc', hM', hb'⟩ := h'
  · exact le_antisymm (not_lt.1 fun h ↦ ht' _ h hs) (not_lt.1 fun h ↦ hs' _ h ht)
  · exact (hmin ht ht' hab' hc hc' hM').elim
  · exact (hmin hs hs' hab ha ha' hM).elim
  · obtain rfl : a = a' :=
      le_antisymm (le_of_forall_mem_Ioo hab' hM' ha) (le_of_forall_mem_Ioo hab hM hc)
    have hbb : b = b' := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · obtain ⟨s, h₁, h₂, h₃⟩ := hb b' hlt
        exact h₃ (hM' s h₁ h₂)
      · obtain ⟨s, h₁, h₂, h₃⟩ := hb' b hlt
        exact h₃ (hM s h₁ h₂)
    subst hbb
    linarith

private theorem exists_choicePred {S : Set (σ ⊕ Unit → ℝ)} (hS : IsSemialgebraic S)
    (hS₁ : ∀ z ∈ S, |z (Sum.inr ())| < 1) {x : σ → ℝ} {t₀ : ℝ}
    (ht₀ : Sum.elim x (fun _ ↦ t₀) ∈ S) : ∃ t, ChoicePred S x t := by
  set A := {t : ℝ | Sum.elim x (fun _ ↦ t) ∈ S}
  have hA₁ (t) (ht : t ∈ A) : |t| < 1 := hS₁ _ ht
  have hbdd : BddBelow A := ⟨-1, fun t ht ↦ by linarith [neg_abs_le t, hA₁ t ht]⟩
  have hne : A.Nonempty := ⟨t₀, ht₀⟩
  set a := sInf A
  have hlow (s) (hs : s < a) : s ∉ A := fun h ↦ (csInf_le hbdd h).not_gt hs
  by_cases ha : a ∈ A
  · exact ⟨a, .inl ⟨ha, hlow⟩⟩
  -- Right of `a`, the fiber contains an interval `(a, c₀)`.
  obtain ⟨c₀, hac₀, hc₀⟩ : ∃ c₀, a < c₀ ∧ ∀ s, a < s → s < c₀ → s ∈ A := by
    -- The fiber, as a subset of the line `Fin 1 → ℝ`.
    have hA : IsSemialgebraic {v : Fin 1 → ℝ | Sum.elim x (v ∘ fun _ ↦ 0) ∈ S} :=
      (hS.setOf_sumElim_mem x).preimage_comp fun _ ↦ 0
    rcases hA.eventually_nhdsGT_mem_or_notMem a with h | h
    · obtain ⟨c₀, hc₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
      exact ⟨c₀, hc₀, fun s h₁ h₂ ↦ by simpa [A, Function.comp_def] using hsub ⟨h₁, h₂⟩⟩
    · obtain ⟨c₀, hc₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
      obtain ⟨s, hs, hsc⟩ := exists_lt_of_csInf_lt hne (mem_Ioi.1 hc₀)
      have has : a < s := (csInf_le hbdd hs).lt_of_ne fun h ↦ ha (by rwa [show a = s from h])
      exact (hsub ⟨has, hsc⟩ (by simpa [A, Function.comp_def] using hs)).elim
  set B := {c : ℝ | ∀ s, a < s → s < c → s ∈ A}
  have ha₁ : a < 1 := (csInf_le hbdd ht₀).trans_lt (lt_of_abs_lt (hA₁ t₀ ht₀))
  have hBbdd : BddAbove B := ⟨1, fun c hc ↦ not_lt.1 fun h ↦ by
    simpa using hA₁ 1 (hc 1 ha₁ h)⟩
  have hc₀B : c₀ ∈ B := hc₀
  set b := sSup B
  have hab : a < b := hac₀.trans_le (le_csSup hBbdd hc₀B)
  have hM (s) (h₁ : a < s) (h₂ : s < b) : s ∈ A := by
    obtain ⟨c, hc, hsc⟩ := exists_lt_of_lt_csSup ⟨c₀, hc₀B⟩ h₂
    exact hc s h₁ hsc
  refine ⟨(a + b) / 2, .inr ⟨a, b, hab, by ring, hlow, ha, hM, fun c hc ↦ ?_⟩⟩
  by_contra! h
  exact (le_csSup hBbdd (show c ∈ B from h)).not_gt hc

/-- Semialgebraic choice of one coordinate, for a family whose fibers lie in `(-1, 1)`. -/
private theorem exists_isSemialgebraicOn_of_abs_lt_one {S : Set (σ ⊕ Unit → ℝ)}
    (hS : IsSemialgebraic S) (hS₁ : ∀ z ∈ S, |z (Sum.inr ())| < 1) :
    ∃ f : (σ → ℝ) → (Unit → ℝ), IsSemialgebraicOn f {x | ∃ y, Sum.elim x y ∈ S} ∧
      ∀ x ∈ {x | ∃ y, Sum.elim x y ∈ S}, Sum.elim x (f x) ∈ S := by
  classical
  let f : (σ → ℝ) → (Unit → ℝ) := fun x _ ↦
    if h : ∃ t, ChoicePred S x t then h.choose else 0
  have hf {x : σ → ℝ} (hx : x ∈ {x | ∃ y, Sum.elim x y ∈ S}) : ChoicePred S x (f x ()) := by
    obtain ⟨y, hy⟩ := hx
    have h : ∃ t, ChoicePred S x t := exists_choicePred hS hS₁ (t₀ := y ()) hy
    simpa only [f, dite_eq_left h] using h.choose_spec
  refine ⟨f, isSemialgebraicOn_of_setOf_iff (G := fun x y ↦ ChoicePred S x (y ()))
    (isSemialgebraic_choicePred hS) fun x y ↦ ?_, fun x hx ↦ (hf hx).mem⟩
  refine ⟨fun h ↦ ?_, fun ⟨hx, hy⟩ ↦ hy ▸ hf hx⟩
  have hx : x ∈ {x | ∃ y, Sum.elim x y ∈ S} := ⟨fun _ ↦ y (), h.mem⟩
  exact ⟨hx, funext fun _ ↦ (hf hx).unique h⟩

/-- The graph `u * (1 + |t|) = t` of `t ↦ t / (1 + |t|)`, in two coordinates `u = z i` and
`t = z j`, is semialgebraic. -/
theorem isSemialgebraic_setOf_mul_one_add_abs_eq [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] (i j : σ) :
    IsSemialgebraic {z : σ → R | z i * (1 + |z j|) = z j} := by
  refine isSemialgebraic_setOf_of_iff (((isSemialgebraic_eval_nonneg (X j)).inter
    (isSemialgebraic_eval_eq (X i * (1 + X j)) (X j))).union ((isSemialgebraic_eval_neg (X j)).inter
    (isSemialgebraic_eval_eq (X i * (1 - X j)) (X j)))) fun z ↦ ?_
  rcases le_or_gt 0 (z j) with h | h
  · simp [abs_of_nonneg h, h, h.not_gt]
  · simp [abs_of_neg h, h, h.not_ge, sub_eq_add_neg]

/-- The map `u ↦ u / (1 - |u|)`, on the points `u : Unit → R` with `|u ()| < 1`, is
semialgebraic. -/
theorem isSemialgebraicOn_div_one_sub_abs [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [HasSemialgebraicProjections R] :
    IsSemialgebraicOn (fun (u : Unit → R) (_ : Unit) ↦ u () / (1 - |u ()|)) {u | |u ()| < 1} :=
  isSemialgebraicOn_of_setOf_iff (G := fun u t ↦ u () * (1 + |t ()|) = t ())
    (isSemialgebraic_setOf_mul_one_add_abs_eq (Sum.inl ()) (Sum.inr ())) fun u t ↦ by
      simp [mul_one_add_abs_eq_iff, funext_iff, Unique.forall_iff]

/-- **Semialgebraic choice** for one coordinate: a semialgebraic family `S` of subsets of `ℝ`,
indexed by `x : σ → ℝ`, has a semialgebraic section over the set of parameters whose fiber is
nonempty. -/
theorem IsSemialgebraic.exists_isSemialgebraicOn_sumElim_mem_unit {S : Set (σ ⊕ Unit → ℝ)}
    (hS : IsSemialgebraic S) :
    ∃ f : (σ → ℝ) → (Unit → ℝ), IsSemialgebraicOn f {x | ∃ y, Sum.elim x y ∈ S} ∧
      ∀ x ∈ {x | ∃ y, Sum.elim x y ∈ S}, Sum.elim x (f x) ∈ S := by
  -- Move the fibers into `(-1, 1)` by `t ↦ t / (1 + |t|)`, choose there, and move back.
  set S' := {z : σ ⊕ Unit → ℝ |
    ∃ t, Sum.elim (z ∘ Sum.inl) (fun _ ↦ t) ∈ S ∧ z (Sum.inr ()) * (1 + |t|) = t}
  have hS' : IsSemialgebraic S' := by
    refine IsSemialgebraic.setOf_exists_scalar (isSemialgebraic_setOf_and ?_ ?_)
    · exact isSemialgebraic_setOf_mem_of_eq_comp hS
        (Sum.elim (Sum.inl ∘ Sum.inl) fun _ ↦ Sum.inr ()) fun z ↦ by ext (i | i) <;> rfl
    · exact isSemialgebraic_setOf_mul_one_add_abs_eq (Sum.inl (Sum.inr ())) (Sum.inr ())
  have hS'₁ (z) (hz : z ∈ S') : |z (Sum.inr ())| < 1 := by
    obtain ⟨t, -, ht⟩ := hz
    exact (mul_one_add_abs_eq_iff.1 ht).1
  have hdom : {x | ∃ y, Sum.elim x y ∈ S'} = {x | ∃ y, Sum.elim x y ∈ S} := by
    ext x
    refine ⟨fun ⟨y, t, ht, _⟩ ↦ ⟨fun _ ↦ t, by simpa using ht⟩, fun ⟨y, hy⟩ ↦ ?_⟩
    refine ⟨fun _ ↦ y () / (1 + |y ()|), y (), hy, ?_⟩
    simp only [Sum.elim_inr]
    field_simp
  obtain ⟨g, hg, hgS⟩ := exists_isSemialgebraicOn_of_abs_lt_one hS' hS'₁
  rw [hdom] at hg hgS
  refine ⟨_, isSemialgebraicOn_div_one_sub_abs.comp hg fun x hx ↦ by
    simpa using hS'₁ _ (hgS x hx), fun x hx ↦ ?_⟩
  obtain ⟨t, ht, hgt⟩ := hgS x hx
  simp only [Sum.elim_comp_inl, Sum.elim_inr] at ht hgt
  simpa only [Function.comp_apply, (mul_one_add_abs_eq_iff.1 hgt).2] using ht

/-! ### Finitely many output coordinates -/

section Finite

/-- Semialgebraic choice transfers along a bijection `τ ≃ τ'` of the output coordinates. -/
private theorem exists_isSemialgebraicOn_sumElim_mem_of_equiv {τ' : Type*} (e : τ ≃ τ')
    (h : ∀ S : Set (σ ⊕ τ → ℝ), IsSemialgebraic S →
      ∃ f : (σ → ℝ) → (τ → ℝ), IsSemialgebraicOn f {x | ∃ y, Sum.elim x y ∈ S} ∧
        ∀ x ∈ {x | ∃ y, Sum.elim x y ∈ S}, Sum.elim x (f x) ∈ S)
    (S : Set (σ ⊕ τ' → ℝ)) (hS : IsSemialgebraic S) :
    ∃ f : (σ → ℝ) → (τ' → ℝ), IsSemialgebraicOn f {x | ∃ y, Sum.elim x y ∈ S} ∧
      ∀ x ∈ {x | ∃ y, Sum.elim x y ∈ S}, Sum.elim x (f x) ∈ S := by
  have key (x : σ → ℝ) (y : τ → ℝ) :
      Sum.elim x y ∘ Sum.elim Sum.inl (Sum.inr ∘ e.symm) = Sum.elim x (y ∘ e.symm) := by
    ext (i | i) <;> rfl
  obtain ⟨f, hf, hfS⟩ := h _ (hS.preimage_comp (Sum.elim Sum.inl (Sum.inr ∘ e.symm)))
  have hdom : {x | ∃ y, Sum.elim x y ∈
      (fun z ↦ z ∘ Sum.elim Sum.inl (Sum.inr ∘ e.symm)) ⁻¹' S} =
      {x | ∃ y, Sum.elim x y ∈ S} := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, key]
    exact ⟨fun ⟨y, hy⟩ ↦ ⟨_, hy⟩, fun ⟨y, hy⟩ ↦ ⟨y ∘ e, by simpa [Function.comp_assoc] using hy⟩⟩
  rw [hdom] at hf hfS
  refine ⟨fun x ↦ f x ∘ e.symm, (isSemialgebraicOn_comp_equiv_iff e.symm).2 hf, fun x hx ↦ ?_⟩
  simpa only [mem_preimage, key] using hfS x hx

/-- Semialgebraic choice with no output coordinates. -/
private theorem exists_isSemialgebraicOn_sumElim_mem_of_isEmpty [IsEmpty τ]
    (S : Set (σ ⊕ τ → ℝ)) (hS : IsSemialgebraic S) :
    ∃ f : (σ → ℝ) → (τ → ℝ), IsSemialgebraicOn f {x | ∃ y, Sum.elim x y ∈ S} ∧
      ∀ x ∈ {x | ∃ y, Sum.elim x y ∈ S}, Sum.elim x (f x) ∈ S := by
  refine ⟨fun _ ↦ isEmptyElim, isSemialgebraicOn_const _ hS.setOf_exists_sumElim, ?_⟩
  rintro x ⟨y, hy⟩
  rwa [Subsingleton.elim y isEmptyElim] at hy

/-- Semialgebraic choice for the output coordinates `α ⊕ Unit` follows from semialgebraic choice
for `α`: choose the coordinates `α` over the projection that forgets the last one, then the last
one by `IsSemialgebraic.exists_isSemialgebraicOn_sumElim_mem_unit`. -/
private theorem exists_isSemialgebraicOn_sumElim_mem_sum_unit {α : Type*} [Finite α]
    (h : ∀ S : Set (σ ⊕ α → ℝ), IsSemialgebraic S →
      ∃ f : (σ → ℝ) → (α → ℝ), IsSemialgebraicOn f {x | ∃ y, Sum.elim x y ∈ S} ∧
        ∀ x ∈ {x | ∃ y, Sum.elim x y ∈ S}, Sum.elim x (f x) ∈ S)
    (S : Set (σ ⊕ (α ⊕ Unit) → ℝ)) (hS : IsSemialgebraic S) :
    ∃ f : (σ → ℝ) → (α ⊕ Unit → ℝ), IsSemialgebraicOn f {x | ∃ y, Sum.elim x y ∈ S} ∧
      ∀ x ∈ {x | ∃ y, Sum.elim x y ∈ S}, Sum.elim x (f x) ∈ S := by
  -- `S` with its coordinates regrouped as `(σ ⊕ α) ⊕ Unit`.
  set r : σ ⊕ (α ⊕ Unit) → (σ ⊕ α) ⊕ Unit :=
    Sum.elim (Sum.inl ∘ Sum.inl) (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr)
  have key (x : σ → ℝ) (y : α → ℝ) (t : Unit → ℝ) :
      Sum.elim (Sum.elim x y) t ∘ r = Sum.elim x (Sum.elim y t) := by
    ext (i | i | i) <;> rfl
  set S₁ : Set ((σ ⊕ α) ⊕ Unit → ℝ) := (fun w ↦ w ∘ r) ⁻¹' S
  set T := {w : σ ⊕ α → ℝ | ∃ t, Sum.elim w t ∈ S₁}
  have hT : IsSemialgebraic T := (hS.preimage_comp r).setOf_exists_sumElim
  obtain ⟨g, hg, hgS⟩ := (hS.preimage_comp r).exists_isSemialgebraicOn_sumElim_mem_unit
  obtain ⟨f₁, hf₁, hf₁T⟩ := h T hT
  have hdom : {x | ∃ y, Sum.elim x y ∈ T} = {x | ∃ y, Sum.elim x y ∈ S} := by
    ext x
    simp only [T, S₁, mem_ofPred_eq, mem_preimage, key]
    refine ⟨fun ⟨y, t, h⟩ ↦ ⟨_, h⟩, fun ⟨y, h⟩ ↦ ⟨y ∘ Sum.inl, y ∘ Sum.inr, ?_⟩⟩
    rwa [Sum.elim_comp_inl_inr]
  rw [hdom] at hf₁ hf₁T
  refine ⟨fun x ↦ Sum.elim (f₁ x) (g (Sum.elim x (f₁ x))), ?_, fun x hx ↦ ?_⟩
  · -- The graph is cut out by the graphs of `f₁` and of `g`, without a projection.
    refine isSemialgebraicOn_of_setOf_iff (G := fun x y ↦
      (x ∈ {x | ∃ y, Sum.elim x y ∈ S} ∧ f₁ x = y ∘ Sum.inl) ∧
        (Sum.elim x (y ∘ Sum.inl) ∈ T ∧ g (Sum.elim x (y ∘ Sum.inl)) = y ∘ Sum.inr))
      ?_ fun x y ↦ ?_
    · convert (hf₁.graph.preimage_comp (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl))).inter
        (hg.graph.preimage_comp
          (Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)) (Sum.inr ∘ Sum.inr))) using 1
      ext z
      rw [mem_inter_iff, mem_preimage, mem_preimage_sumArrowEquivProdArrow_graphOn, mem_preimage,
        mem_preimage_sumArrowEquivProdArrow_graphOn]
      simp only [mem_ofPred_eq, Function.comp_assoc, Sum.elim_comp_inl, Sum.elim_comp_inr,
        Sum.comp_elim, T, S₁]
    · constructor
      · rintro ⟨⟨hx, hfy⟩, -, hgy⟩
        refine ⟨hx, ?_⟩
        rw [hfy, hgy, Sum.elim_comp_inl_inr]
      · rintro ⟨hx, rfl⟩
        simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
        exact ⟨⟨hx, trivial⟩, hf₁T x hx, trivial⟩
  · simpa only [S₁, mem_preimage, key] using hgS _ (hf₁T x hx)

end Finite

/-- **Semialgebraic choice**: a semialgebraic family `S` of subsets of `ℝ^τ`, `τ` finite,
indexed by `x : σ → ℝ`, has a semialgebraic section over the set of parameters whose fiber is
nonempty. -/
theorem IsSemialgebraic.exists_isSemialgebraicOn_sumElim_mem [Finite τ] {S : Set (σ ⊕ τ → ℝ)}
    (hS : IsSemialgebraic S) :
    ∃ f : (σ → ℝ) → (τ → ℝ), IsSemialgebraicOn f {x | ∃ y, Sum.elim x y ∈ S} ∧
      ∀ x ∈ {x | ∃ y, Sum.elim x y ∈ S}, Sum.elim x (f x) ∈ S := by
  induction τ using Finite.induction_empty_option with
  | of_equiv e h => exact exists_isSemialgebraicOn_sumElim_mem_of_equiv e (fun S hS ↦ h hS) S hS
  | h_empty => exact exists_isSemialgebraicOn_sumElim_mem_of_isEmpty S hS
  | h_option h =>
    exact exists_isSemialgebraicOn_sumElim_mem_of_equiv (Equiv.optionEquivSumPUnit _).symm
      (exists_isSemialgebraicOn_sumElim_mem_sum_unit fun S hS ↦ h hS) S hS

end TauCeti

end

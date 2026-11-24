/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.RealAlgebraic.Semialgebraic.OneVariable

/-!
# Semialgebraic choice

A semialgebraic family of subsets of `ℝ`, given as a semialgebraic set
`S : Set (σ ⊕ Unit → ℝ)` whose fiber over `x : σ → ℝ` is `{t | Sum.elim x (fun _ ↦ t) ∈ S}`, has a
semialgebraic section: a function `f`, semialgebraic on the set of parameters with nonempty fiber,
with `Sum.elim x (f x) ∈ S` there. This is definable choice for one coordinate.

* `TauCeti.IsSemialgebraic.exists_isSemialgebraicOn_sumElim_mem_unit`: semialgebraic choice for
  one output coordinate. The parameters `σ` need not be finite.

## Proof

First assume that every fiber lies in `(-1, 1)`. Let `a` be the infimum of a nonempty fiber. If
`a` lies in the fiber, choose `a`. Otherwise the fiber contains every point just right of `a`
(`TauCeti.IsSemialgebraic.eventually_nhdsGT_mem_or_notMem`), hence an interval `(a, b)` that no
longer interval `(a, c)` extends, and we choose its midpoint. Both alternatives are expressed by
one first-order formula in the coordinates, with quantifiers over single real numbers, which
determines the chosen point; so the graph of the choice is semialgebraic, by
`TauCeti.IsSemialgebraic.setOf_exists_sumElim` and `TauCeti.IsSemialgebraic.setOf_forall_sumElim`
for the quantifiers and `TauCeti.IsSemialgebraic.preimage_comp` for the changes of coordinates.
In general, the homeomorphism `t ↦ t / (1 + |t|)` of `ℝ` onto `(-1, 1)`, whose graph is the
semialgebraic set `u * (1 + |t|) = t`, moves the fibers into `(-1, 1)`, and the inverse
`u ↦ u / (1 - |u|)` brings the chosen point back.

## References

* L. van den Dries, *Tame Topology and o-minimal Structures*, Cambridge University Press, 1998,
  Chapter 6, Section 1.
* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998, Sections 2.3–2.4.
-/

public section

open Set Topology MvPolynomial

namespace TauCeti

variable {σ : Type*}

/-! ### Sets cut out by formulas in one more coordinate -/

private theorem isSemialgebraic_setOf_of_iff {P : (σ → ℝ) → Prop} {s : Set (σ → ℝ)}
    (hs : IsSemialgebraic s) (h : ∀ z, P z ↔ z ∈ s) : IsSemialgebraic {z | P z} := by
  convert hs using 1
  ext z
  exact h z

private theorem isSemialgebraic_setOf_mem_of_eq_comp {τ : Type*} {s : Set (τ → ℝ)}
    (hs : IsSemialgebraic s) (e : τ → σ) {g : (σ → ℝ) → τ → ℝ} (hg : ∀ z, g z = z ∘ e) :
    IsSemialgebraic {z | g z ∈ s} :=
  isSemialgebraic_setOf_of_iff (hs.preimage_comp e) fun z ↦ by simp [hg]

private theorem isSemialgebraic_setOf_and {P Q : (σ → ℝ) → Prop}
    (hP : IsSemialgebraic {z | P z}) (hQ : IsSemialgebraic {z | Q z}) :
    IsSemialgebraic {z | P z ∧ Q z} :=
  hP.inter hQ

private theorem isSemialgebraic_setOf_or {P Q : (σ → ℝ) → Prop}
    (hP : IsSemialgebraic {z | P z}) (hQ : IsSemialgebraic {z | Q z}) :
    IsSemialgebraic {z | P z ∨ Q z} :=
  hP.union hQ

private theorem isSemialgebraic_setOf_not {P : (σ → ℝ) → Prop}
    (hP : IsSemialgebraic {z | P z}) : IsSemialgebraic {z | ¬ P z} :=
  hP.compl

private theorem isSemialgebraic_setOf_imp {P Q : (σ → ℝ) → Prop}
    (hP : IsSemialgebraic {z | P z}) (hQ : IsSemialgebraic {z | Q z}) :
    IsSemialgebraic {z | P z → Q z} :=
  isSemialgebraic_setOf_of_iff (hP.compl.union hQ) fun z ↦ by
    simp [imp_iff_not_or]

private theorem isSemialgebraic_setOf_exists {P : (σ → ℝ) → ℝ → Prop}
    (h : IsSemialgebraic {z : σ ⊕ Unit → ℝ | P (z ∘ Sum.inl) (z (Sum.inr ()))}) :
    IsSemialgebraic {x : σ → ℝ | ∃ t, P x t} :=
  isSemialgebraic_setOf_of_iff h.setOf_exists_sumElim fun x ↦ by
    simp only [mem_ofPred_eq, Sum.elim_comp_inl, Sum.elim_inr]
    exact ⟨fun ⟨t, ht⟩ ↦ ⟨fun _ ↦ t, ht⟩, fun ⟨y, hy⟩ ↦ ⟨y (), hy⟩⟩

private theorem isSemialgebraic_setOf_forall {P : (σ → ℝ) → ℝ → Prop}
    (h : IsSemialgebraic {z : σ ⊕ Unit → ℝ | P (z ∘ Sum.inl) (z (Sum.inr ()))}) :
    IsSemialgebraic {x : σ → ℝ | ∀ t, P x t} :=
  isSemialgebraic_setOf_of_iff h.setOf_forall_sumElim fun x ↦ by
    simp only [mem_ofPred_eq, Sum.elim_comp_inl, Sum.elim_inr]
    exact ⟨fun h y ↦ h (y ()), fun h t ↦ h fun _ ↦ t⟩

private theorem isSemialgebraic_setOf_lt (i j : σ) : IsSemialgebraic {z : σ → ℝ | z i < z j} :=
  isSemialgebraic_setOf_of_iff (isSemialgebraic_eval_lt (X i) (X j)) fun z ↦ by simp

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
  · refine isSemialgebraic_setOf_forall (isSemialgebraic_setOf_imp ?_ ?_)
    · exact isSemialgebraic_setOf_lt _ _
    · exact isSemialgebraic_setOf_not (isSemialgebraic_setOf_mem_of_eq_comp hS
        (Sum.elim (Sum.inl ∘ Sum.inl) fun _ ↦ Sum.inr ()) fun z ↦ by ext (i | i) <;> rfl)
  · refine isSemialgebraic_setOf_exists (isSemialgebraic_setOf_exists ?_)
    refine isSemialgebraic_setOf_and ?_ (isSemialgebraic_setOf_and ?_
      (isSemialgebraic_setOf_and ?_ (isSemialgebraic_setOf_and ?_
        (isSemialgebraic_setOf_and ?_ ?_))))
    · exact isSemialgebraic_setOf_lt (Sum.inl (Sum.inr ())) (Sum.inr ())
    · exact isSemialgebraic_setOf_of_iff
        (isSemialgebraic_eval_eq (2 * X (Sum.inl (Sum.inl (Sum.inr ()))))
          (X (Sum.inl (Sum.inr ())) + X (Sum.inr ()))) fun z ↦ by simp
    · refine isSemialgebraic_setOf_forall (isSemialgebraic_setOf_imp ?_ ?_)
      · exact isSemialgebraic_setOf_lt (Sum.inr ()) (Sum.inl (Sum.inl (Sum.inr ())))
      · exact isSemialgebraic_setOf_not (isSemialgebraic_setOf_mem_of_eq_comp hS
          (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ Sum.inl) fun _ ↦ Sum.inr ())
          fun z ↦ by ext (i | i) <;> rfl)
    · exact isSemialgebraic_setOf_not (isSemialgebraic_setOf_mem_of_eq_comp hS
        (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl) fun _ ↦ Sum.inl (Sum.inr ()))
        fun z ↦ by ext (i | i) <;> rfl)
    · refine isSemialgebraic_setOf_forall (isSemialgebraic_setOf_imp ?_
        (isSemialgebraic_setOf_imp ?_ ?_))
      · exact isSemialgebraic_setOf_lt (Sum.inl (Sum.inl (Sum.inr ()))) (Sum.inr ())
      · exact isSemialgebraic_setOf_lt (Sum.inr ()) (Sum.inl (Sum.inr ()))
      · exact isSemialgebraic_setOf_mem_of_eq_comp hS
          (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ Sum.inl) fun _ ↦ Sum.inr ())
          fun z ↦ by ext (i | i) <;> rfl
    · refine isSemialgebraic_setOf_forall (isSemialgebraic_setOf_imp ?_
        (isSemialgebraic_setOf_exists (isSemialgebraic_setOf_and ?_
          (isSemialgebraic_setOf_and ?_ ?_))))
      · exact isSemialgebraic_setOf_lt (Sum.inl (Sum.inr ())) (Sum.inr ())
      · exact isSemialgebraic_setOf_lt (Sum.inl (Sum.inl (Sum.inl (Sum.inr ())))) (Sum.inr ())
      · exact isSemialgebraic_setOf_lt (Sum.inr ()) (Sum.inl (Sum.inr ()))
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

/-- A fiber of a semialgebraic family is semialgebraic as a subset of the line `Fin 1 → ℝ`. -/
private theorem isSemialgebraic_fiber {S : Set (σ ⊕ Unit → ℝ)} (hS : IsSemialgebraic S)
    (x : σ → ℝ) : IsSemialgebraic {v : Fin 1 → ℝ | Sum.elim x (fun _ ↦ v 0) ∈ S} := by
  refine isSemialgebraic_setOf_of_iff
    (hS.preimage_eval (Sum.elim (fun i ↦ C (x i)) fun _ ↦ X 0)) fun v ↦ ?_
  rw [mem_preimage]
  convert Iff.rfl using 2
  ext (i | i) <;> simp

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
    rcases (isSemialgebraic_fiber hS x).eventually_nhdsGT_mem_or_notMem a with h | h
    · obtain ⟨c₀, hc₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
      exact ⟨c₀, hc₀, fun s h₁ h₂ ↦ by simpa [A] using hsub ⟨h₁, h₂⟩⟩
    · obtain ⟨c₀, hc₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
      obtain ⟨s, hs, hsc⟩ := exists_lt_of_csInf_lt hne (mem_Ioi.1 hc₀)
      have has : a < s := (csInf_le hbdd hs).lt_of_ne fun h ↦ ha (by rwa [show a = s from h])
      exact (hsub ⟨has, hsc⟩ (by simpa [A] using hs)).elim
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

/-- A function of one output coordinate is semialgebraic on `D` if its graph over `D` is cut out
by a semialgebraic formula. -/
private theorem isSemialgebraicOn_of_iff {D : Set (σ → ℝ)} {f : (σ → ℝ) → Unit → ℝ}
    {G : (σ → ℝ) → ℝ → Prop}
    (hG : IsSemialgebraic {z : σ ⊕ Unit → ℝ | G (z ∘ Sum.inl) (z (Sum.inr ()))})
    (h : ∀ x t, G x t ↔ x ∈ D ∧ f x () = t) : IsSemialgebraicOn f D := by
  refine isSemialgebraicOn_iff_graph.2 (isSemialgebraic_setOf_of_iff hG fun z ↦ ?_)
  refine mem_preimage_sumArrowEquivProdArrow_graphOn.trans ?_
  refine Iff.trans ?_ (h _ _).symm
  rw [funext_iff, Unique.forall_iff]
  rfl

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
  refine ⟨f, isSemialgebraicOn_of_iff (isSemialgebraic_choicePred hS) fun x t ↦ ?_,
    fun x hx ↦ (hf hx).mem⟩
  refine ⟨fun h ↦ ?_, fun ⟨hx, ht⟩ ↦ ht ▸ hf hx⟩
  have hx : x ∈ {x | ∃ y, Sum.elim x y ∈ S} := ⟨fun _ ↦ t, h.mem⟩
  exact ⟨hx, (hf hx).unique h⟩

/-- If `u * (1 + |t|) = t`, then `|u| < 1` and `t = u / (1 - |u|)`. -/
private theorem abs_lt_one_and_eq_div_of_mul_one_add_abs_eq {u t : ℝ}
    (h : u * (1 + |t|) = t) : |u| < 1 ∧ t = u / (1 - |u|) := by
  have hpos : 0 < 1 + |t| := by positivity
  have habs : |u| * (1 + |t|) = |t| := by
    rw [← abs_of_pos hpos, ← abs_mul, h]
  have hu : |u| < 1 := by nlinarith [abs_nonneg t]
  refine ⟨hu, eq_div_of_mul_eq (by linarith) ?_⟩
  -- `t * |u| = u * |t|`, since both equal `|u| * u * (1 + |t|)`.
  have : t * |u| = u * |t| := by
    calc t * |u| = u * (|u| * (1 + |t|)) := by nth_rewrite 1 [← h]; ring
      _ = u * |t| := by rw [habs]
  linarith

private theorem isSemialgebraic_setOf_mul_one_add_abs_eq (i j : σ) :
    IsSemialgebraic {z : σ → ℝ | z i * (1 + |z j|) = z j} := by
  refine isSemialgebraic_setOf_of_iff (((isSemialgebraic_eval_nonneg (X j)).inter
    (isSemialgebraic_eval_eq (X i * (1 + X j)) (X j))).union ((isSemialgebraic_eval_neg (X j)).inter
    (isSemialgebraic_eval_eq (X i * (1 - X j)) (X j)))) fun z ↦ ?_
  rcases le_or_gt 0 (z j) with h | h
  · simp [abs_of_nonneg h, h, h.not_gt]
  · simp [abs_of_neg h, h, h.not_ge, sub_eq_add_neg]

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
    refine isSemialgebraic_setOf_exists (isSemialgebraic_setOf_and ?_ ?_)
    · exact isSemialgebraic_setOf_mem_of_eq_comp hS
        (Sum.elim (Sum.inl ∘ Sum.inl) fun _ ↦ Sum.inr ()) fun z ↦ by ext (i | i) <;> rfl
    · exact isSemialgebraic_setOf_mul_one_add_abs_eq (Sum.inl (Sum.inr ())) (Sum.inr ())
  have hS'₁ (z) (hz : z ∈ S') : |z (Sum.inr ())| < 1 := by
    obtain ⟨t, -, ht⟩ := hz
    exact (abs_lt_one_and_eq_div_of_mul_one_add_abs_eq ht).1
  have hdom : {x | ∃ y, Sum.elim x y ∈ S'} = {x | ∃ y, Sum.elim x y ∈ S} := by
    ext x
    refine ⟨fun ⟨y, t, ht, _⟩ ↦ ⟨fun _ ↦ t, by simpa using ht⟩, fun ⟨y, hy⟩ ↦ ?_⟩
    refine ⟨fun _ ↦ y () / (1 + |y ()|), y (), hy, ?_⟩
    simp only [Sum.elim_inr]
    field_simp
  obtain ⟨g, hg, hgS⟩ := exists_isSemialgebraicOn_of_abs_lt_one hS' hS'₁
  rw [hdom] at hg hgS
  have hgt {x} (hx : x ∈ {x | ∃ y, Sum.elim x y ∈ S}) :
      Sum.elim x (fun _ ↦ g x () / (1 - |g x ()|)) ∈ S := by
    obtain ⟨t, ht, hgt⟩ := hgS x hx
    simp only [Sum.elim_comp_inl, Sum.elim_inr] at ht hgt
    rwa [← (abs_lt_one_and_eq_div_of_mul_one_add_abs_eq hgt).2]
  refine ⟨fun x _ ↦ g x () / (1 - |g x ()|), isSemialgebraicOn_of_iff
    (G := fun x t ↦ Sum.elim x (fun _ ↦ t) ∈ S ∧ ∃ u, Sum.elim x (fun _ ↦ u) ∈
      Equiv.sumArrowEquivProdArrow σ Unit ℝ ⁻¹' {x | ∃ y, Sum.elim x y ∈ S}.graphOn g ∧
      u * (1 + |t|) = t) ?_ fun x t ↦ ?_, fun x hx ↦ hgt hx⟩
  · refine isSemialgebraic_setOf_and ?_ (isSemialgebraic_setOf_exists
      (isSemialgebraic_setOf_and ?_ ?_))
    · exact isSemialgebraic_setOf_mem_of_eq_comp hS id fun z ↦ by ext (i | i) <;> rfl
    · exact isSemialgebraic_setOf_mem_of_eq_comp hg.graph
        (Sum.elim (Sum.inl ∘ Sum.inl) fun _ ↦ Sum.inr ()) fun z ↦ by ext (i | i) <;> rfl
    · exact isSemialgebraic_setOf_mul_one_add_abs_eq (Sum.inr ()) (Sum.inl (Sum.inr ()))
  · simp only [mem_preimage_sumArrowEquivProdArrow_graphOn, Sum.elim_comp_inl, Sum.elim_comp_inr,
      funext_iff, Unique.forall_iff]
    refine ⟨fun ⟨_, u, ⟨hx, hu⟩, hut⟩ ↦ ⟨hx, ?_⟩, fun ⟨hx, ht⟩ ↦ ⟨ht ▸ hgt hx, ?_⟩⟩
    · rw [(abs_lt_one_and_eq_div_of_mul_one_add_abs_eq hut).2, ← hu]
    · obtain ⟨t', ht', hgt'⟩ := hgS x hx
      simp only [Sum.elim_comp_inl, Sum.elim_inr] at ht' hgt'
      refine ⟨g x (), ⟨hx, rfl⟩, ?_⟩
      rwa [← ht, ← (abs_lt_one_and_eq_div_of_mul_one_add_abs_eq hgt').2]

end TauCeti

end

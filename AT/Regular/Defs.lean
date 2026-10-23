import AT.Fullness

/-!
# Regular heaps and admissible maps (paper §5.1–5.2)

* `AT.TokenClass.IsRegularHeap` — the heap, as a `Language (A ⊕ E)`, is regular.
* `AT.RegTS E` — the full subcategory `RegTS_E` of finite carriers with regular heaps.
* **Example 5.1** (`AT.shapeHeapGap`): regular shapes, nonregular heap.
* **Proposition 5.2** (`AT.RegTS.decidableHom`, `AT.RegTS.homFintype`): effective hom-sets.
  (The complexity-class assertions PSPACE/polynomial are not formalized.)
-/

universe u v

namespace AT

open CategoryTheory

variable {E : Type v}

/-- The heap of a Token class, as a language over the tagged alphabet `A ⊕ E`. -/
def TokenClass.lang (T : TokenClass.{u} E) : Language (T.carrier ⊕ E) := T.heap

/-- A Token class has a regular heap. -/
def TokenClass.IsRegularHeap (T : TokenClass.{u} E) : Prop := T.lang.IsRegular

/-- The objects of `RegTS_E`: finite carrier and regular heap. -/
def isRegTS (E : Type v) : ObjectProperty (TokenClass.{u} E) :=
  fun T => Finite T.carrier ∧ T.IsRegularHeap

/-- `RegTS_E`, the full subcategory of `TS_E` on finite carriers with regular heaps. -/
abbrev RegTS (E : Type v) := (isRegTS.{u} E).FullSubcategory

/-- **Example 5.1** (regular shapes with a nonregular heap): `E = {p}`, `A = {a,b}`,
`H = {p aⁿ bⁿ}` is not regular, although `sh(H) = p(□□)^*` and `L = p□^*` are regular. -/
def shapeHeapGap : TokenClass.{0} Unit where
  carrier := Bool
  heap := {w | ∃ n, w = Sum.inr () :: (List.replicate n (Sum.inl false) ++ List.replicate n (Sum.inl true))}

/-- Two-block words `aⁿ bᵐ` with `a ≠ b` are determined by their block lengths. -/
lemma replicate_append_replicate_inj {α : Type*} [DecidableEq α] {a b : α} (hab : a ≠ b)
    {n m k : ℕ}
    (h : List.replicate n a ++ List.replicate m b = List.replicate k a ++ List.replicate k b) :
    n = k ∧ m = k := by
  have h1 := congrArg (List.count a) h
  have h2 := congrArg List.length h
  simp [List.count_append, List.count_replicate, hab.symm] at h1
  simp at h2
  omega

theorem shapeHeapGap_not_regular : ¬ shapeHeapGap.IsRegularHeap := by
  intro hreg
  have hfin := hreg.finite_range_leftQuotient
  dsimp only [TokenClass.IsRegularHeap, TokenClass.lang, shapeHeapGap] at hfin ⊢
  let x : ℕ → Word Bool Unit := fun n => Sum.inr () :: List.replicate n (Sum.inl false)
  set L : Language (Bool ⊕ Unit) :=
    {w | ∃ n, w = Sum.inr () :: (List.replicate n (Sum.inl false) ++
      List.replicate n (Sum.inl true))} with hL
  have hinj : Function.Injective (L.leftQuotient ∘ x) := by
    intro n m hnm
    have hmem : List.replicate n (Sum.inl true) ∈ (L.leftQuotient ∘ x) n := by
      show _ ∈ L.leftQuotient _
      rw [Language.mem_leftQuotient]
      exact ⟨n, by simp [x]⟩
    rw [hnm] at hmem
    obtain ⟨k, hk⟩ := hmem
    simp only [x, List.cons_append, List.cons.injEq, true_and] at hk
    have := replicate_append_replicate_inj (by simp) hk
    omega
  exact Set.infinite_range_of_injective hinj (hfin.subset (Set.range_comp_subset_range _ _))

/-- A four-state DFA for `p (□□)^*` over `PUnit ⊕ Unit`: `0` start, `1` even, `2` odd, `3` dead. -/
def gapShapeDFA : DFA (PUnit.{1} ⊕ Unit) (Fin 4) where
  step s x :=
    match s.val, x with
    | 0, Sum.inr _ => 1
    | 1, Sum.inl _ => 2
    | 2, Sum.inl _ => 1
    | _, _ => 3
  start := 0
  accept := {1}

lemma gapShapeDFA_evalFrom_dead (w : List (PUnit.{1} ⊕ Unit)) : gapShapeDFA.evalFrom 3 w = 3 := by
  induction w with
  | nil => rfl
  | cons x w ih => rcases x with x | x <;> exact ih

lemma gapShapeDFA_evalFrom_replicate (m : ℕ) :
    gapShapeDFA.evalFrom 1 (List.replicate m (Sum.inl PUnit.unit)) = (if Even m then 1 else 2) ∧
    gapShapeDFA.evalFrom 2 (List.replicate m (Sum.inl PUnit.unit)) = (if Even m then 2 else 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [List.replicate_succ, DFA.evalFrom_cons]
    have h1 : gapShapeDFA.step 1 (Sum.inl PUnit.unit) = 2 := rfl
    have h2 : gapShapeDFA.step 2 (Sum.inl PUnit.unit) = 1 := rfl
    rw [h1, h2, ih.2, ih.1]
    simp only [Nat.even_add_one]
    constructor <;> split_ifs <;> simp_all

lemma gapShapeDFA_evalFrom_ne_dead (w : List (PUnit.{1} ⊕ Unit)) :
    ∀ s : Fin 4, (s = 1 ∨ s = 2) → gapShapeDFA.evalFrom s w ≠ 3 →
      ∀ x ∈ w, x = Sum.inl PUnit.unit := by
  induction w with
  | nil => intro _ _ _ x hx; simp at hx
  | cons y w ih =>
    intro s hs hne x hx
    rw [DFA.evalFrom_cons] at hne
    rcases y with y | y
    · rcases hx with _ | ⟨_, hx⟩
      · rfl
      · refine ih _ ?_ hne x hx
        rcases hs with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl rfl
    · exfalso
      have : gapShapeDFA.step s (Sum.inr y) = 3 := by
        rcases hs with rfl | rfl <;> rfl
      rw [this, gapShapeDFA_evalFrom_dead] at hne
      exact hne rfl

lemma shape_gapWord (n : ℕ) :
    shape (E := Unit) (Sum.inr () :: (List.replicate n (Sum.inl false) ++
      List.replicate n (Sum.inl true)) : Word Bool Unit) =
    Sum.inr () :: List.replicate (n + n) (Sum.inl PUnit.unit) := by
  simp [shape, wordMap]

theorem shapeHeapGap_shapes_regular :
    (show Language (PUnit ⊕ Unit) from shape '' shapeHeapGap.heap).IsRegular := by
  refine ⟨Fin 4, inferInstance, gapShapeDFA, ?_⟩
  dsimp only [shapeHeapGap]
  ext w
  rw [DFA.mem_accepts]
  constructor
  · intro hw
    have hw : gapShapeDFA.eval w = 1 := hw
    rcases w with _ | ⟨x | ⟨⟩, w⟩
    · exact absurd hw (by decide)
    · have : gapShapeDFA.eval (Sum.inl x :: w) = 3 := gapShapeDFA_evalFrom_dead w
      rw [this] at hw; exact absurd hw (by decide)
    · have hw1 : gapShapeDFA.evalFrom 1 w = 1 := hw
      have hall := gapShapeDFA_evalFrom_ne_dead w 1 (Or.inl rfl) (by rw [hw1]; decide)
      have hrep : w = List.replicate w.length (Sum.inl PUnit.unit) :=
        List.eq_replicate_iff.2 ⟨rfl, hall⟩
      have heven : Even w.length := by
        by_contra hodd
        rw [hrep, (gapShapeDFA_evalFrom_replicate _).1, ite_eq_right hodd] at hw1
        exact absurd hw1 (by decide)
      obtain ⟨n, hn⟩ := heven
      refine ⟨Sum.inr () :: (List.replicate n (Sum.inl false) ++ List.replicate n (Sum.inl true)),
        ⟨n, rfl⟩, ?_⟩
      rw [shape_gapWord, hrep, hn]
  · rintro ⟨v, ⟨n, rfl⟩, rfl⟩
    rw [shape_gapWord]
    show gapShapeDFA.evalFrom 1 _ ∈ ({1} : Set (Fin 4))
    rw [(gapShapeDFA_evalFrom_replicate _).1, ite_eq_left ⟨n, rfl⟩]
    rfl

/-! ### Effective hom-set computation (§5.2) -/

/-- The failure language `H ∩ F_E(f)⁻¹(F_E(B) \ K)` of eq. (5.1). -/
def failureLang {A B : Type u} (f : A → B) (H : Language (A ⊕ E)) (K : Language (B ⊕ E)) :
    Language (A ⊕ E) :=
  H ⊓ (wordMap f ⁻¹' Kᶜ)

theorem failureLang_eq_empty_iff {A B : Type u} (f : A → B) (H : Language (A ⊕ E))
    (K : Language (B ⊕ E)) : failureLang f H K = ⊥ ↔ ∀ w ∈ H, wordMap f w ∈ K := by
  constructor
  · intro h w hw
    by_contra hK
    have : w ∈ failureLang f H K := ⟨hw, hK⟩
    rw [h] at this
    exact this
  · intro h
    ext w
    exact ⟨fun ⟨hw, hK⟩ => hK (h w hw), fun hw => hw.elim⟩

theorem failureLang_isRegular {A B : Type u} (f : A → B) {H : Language (A ⊕ E)}
    {K : Language (B ⊕ E)} (hH : H.IsRegular) (hK : K.IsRegular) :
    (failureLang f H K).IsRegular := by
  refine hH.inf ?_
  obtain ⟨σ, _, M, hM⟩ := hK.compl
  exact ⟨σ, inferInstance, M.comap (Sum.map f id), by rw [DFA.accepts_comap, hM]; rfl⟩

/-- **Proposition 5.2** (decidability): whether a carrier function is a Token map between
regularly presented heaps on finite carriers is decidable. -/
theorem RegTS.hom_decidable [Fintype E] [DecidableEq E] (T₁ T₂ : RegTS.{u} E)
    (f : T₁.obj.carrier → T₂.obj.carrier) :
    Nonempty (Decidable (TokenClass.IsHom T₁.obj T₂.obj f)) :=
  ⟨by
    classical
    exact decidable_of_iff (failureLang f T₁.obj.heap T₂.obj.heap = ⊥)
      (failureLang_eq_empty_iff f T₁.obj.heap T₂.obj.heap)⟩

/-- **Proposition 5.2** (finiteness): `Hom(T_A, T_B)` is finite. -/
instance RegTS.finite_hom (T₁ T₂ : RegTS.{u} E) : Finite (T₁ ⟶ T₂) := by
  have := T₁.property.1
  have := T₂.property.1
  refine Finite.of_injective (fun f : T₁ ⟶ T₂ => f.hom.toFun) fun _ _ h => ?_
  exact InducedCategory.hom_ext (TokenClass.Hom.ext h)

/-- When `A = ∅` there is at most one Token map (all carrier functions agree). -/
instance RegTS.hom_subsingleton (T₁ T₂ : RegTS.{u} E) [h : IsEmpty T₁.obj.carrier] :
    Subsingleton (T₁ ⟶ T₂) :=
  ⟨fun _ _ => InducedCategory.hom_ext (TokenClass.Hom.ext (funext fun a => h.elim a))⟩

/-- There is exactly one candidate when `A = ∅`, and none when `A ≠ ∅` and `B = ∅`.
(The unique candidate `∅ → B` is a Token map iff it carries `H` into `K`; this is automatic
when `H = ∅`, but not in general, hence the hypothesis `hK`.) -/
theorem RegTS.hom_empty_carrier (T₁ T₂ : RegTS.{u} E) (h : IsEmpty T₁.obj.carrier)
    (hK : TokenClass.IsHom T₁.obj T₂.obj h.elim) :
    Nonempty (Unique (T₁ ⟶ T₂)) :=
  ⟨@Unique.mk' _ ⟨⟨⟨h.elim, hK⟩⟩⟩ (RegTS.hom_subsingleton T₁ T₂)⟩

theorem RegTS.hom_to_empty (T₁ T₂ : RegTS.{u} E) (h₁ : Nonempty T₁.obj.carrier)
    (h₂ : IsEmpty T₂.obj.carrier) : IsEmpty (T₁ ⟶ T₂) :=
  ⟨fun f => h₂.false (f.hom.toFun h₁.some)⟩

end AT

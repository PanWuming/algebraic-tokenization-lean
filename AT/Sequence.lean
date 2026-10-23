import AT.Signature

/-!
# Sequence interfaces (paper §9)

* **Proposition 9.1** (`AT.occurrenceLift`): coherent occurrence lifting.
* **Proposition 9.2** (`AT.canonical_monoid`, `AT.transport_identities`): canonical lexical
  transport.
-/

universe u

namespace AT

open CategoryTheory

/-! ### Coherent occurrence records (§9.1) -/

/-- The core `E_n = {r, p₁, …, p_n}`. -/
inductive OccLabel (n : ℕ)
  | row | pos : Fin n → OccLabel n

/-- The heap of `L_n(X)`: position records and complete rows. -/
def occHeap {D : Type u} {n : ℕ} (X : Set (Fin n → D)) : Set (Word (X × Fin n) (OccLabel n)) :=
  {w | ∃ (x : X) (i : Fin n), w = [Sum.inr (.pos i), Sum.inl (x, i)]} ∪
  {w | ∃ x : X, w = Sum.inr .row :: (List.ofFn fun i : Fin n => [Sum.inr (.pos i), Sum.inl (x, i)]).flatten}

/-- `L_n(X)` on `Ω_X = X × {1,…,n}` with position records and complete rows. -/
def occurrenceClass {D : Type u} {n : ℕ} (X : Set (Fin n → D)) : TokenClass.{u} (OccLabel n) where
  carrier := X × Fin n
  heap := occHeap X

/-- The lift `c_F(x,i) = (F x, i)`. -/
def occurrenceLiftFun {D D' : Type u} {n : ℕ} {X : Set (Fin n → D)} {Y : Set (Fin n → D')}
    (F : X → Y) : X × Fin n → Y × Fin n := fun p => (F p.1, p.2)

/-- Flattened lists of two-element blocks determine their second entries. -/
lemma flatten_ofFn_pair_snd {α : Type*} : ∀ {n : ℕ} (a a' b b' : Fin n → α),
    (List.ofFn fun i => [a i, b i]).flatten = (List.ofFn fun i => [a' i, b' i]).flatten →
    ∀ i, b i = b' i
  | 0, _, _, _, _, _, i => i.elim0
  | n + 1, a, a', b, b', h, i => by
    rw [List.ofFn_succ, List.ofFn_succ, List.flatten_cons, List.flatten_cons] at h
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    obtain ⟨-, h2, h3⟩ := h
    refine Fin.cases h2 (fun j => ?_) i
    exact flatten_ofFn_pair_snd (fun j => a j.succ) (fun j => a' j.succ)
      (fun j => b j.succ) (fun j => b' j.succ) h3 j

lemma wordMap_rowRecord {D D' : Type u} {n : ℕ} {X : Set (Fin n → D)} {Y : Set (Fin n → D')}
    (g : X × Fin n → Y × Fin n) (x : X) :
    wordMap (E := OccLabel n) g
        (Sum.inr .row :: (List.ofFn fun i : Fin n => [Sum.inr (.pos i), Sum.inl (x, i)]).flatten) =
      Sum.inr .row :: (List.ofFn fun i : Fin n => [Sum.inr (.pos i), Sum.inl (g (x, i))]).flatten := by
  unfold wordMap
  rw [List.map_cons, List.map_flatten, List.map_ofFn]
  simp [Function.comp_def]

/-- The lift is a Token map. -/
def occurrenceLiftHom {D D' : Type u} {n : ℕ} {X : Set (Fin n → D)} {Y : Set (Fin n → D')}
    (F : X → Y) : occurrenceClass X ⟶ occurrenceClass Y where
  toFun := occurrenceLiftFun F
  preserves w hw := by
    rcases hw with ⟨x, i, rfl⟩ | ⟨x, rfl⟩
    · exact Or.inl ⟨F x, i, rfl⟩
    · exact Or.inr ⟨F x, wordMap_rowRecord (occurrenceLiftFun F) x⟩

/-- Every Token map `L_n(X) → L_n(Y)` is a lift. -/
lemma occurrenceClass_hom_apply {D D' : Type u} {n : ℕ} {X : Set (Fin n → D)}
    {Y : Set (Fin n → D')} (g : X × Fin n → Y × Fin n)
    (hg : ∀ w ∈ occHeap X, wordMap g w ∈ occHeap Y) (x : X) :
    ∃ y : Y, ∀ i, g (x, i) = (y, i) := by
  have h := hg _ (Or.inr ⟨x, rfl⟩)
  rw [wordMap_rowRecord g x] at h
  rcases h with ⟨y, i, hy⟩ | ⟨y, hy⟩
  · simp at hy
  · refine ⟨y, ?_⟩
    simp only [List.cons.injEq, true_and] at hy
    intro i
    have := flatten_ofFn_pair_snd _ _ _ _ hy i
    simpa using this

/-- **Proposition 9.1** (coherent occurrence lifting): functions `X → Y` correspond bijectively
to Token maps `L_n(X) → L_n(Y)`. -/
def occurrenceLift {D D' : Type u} {n : ℕ} (hn : 0 < n) (X : Set (Fin n → D)) (Y : Set (Fin n → D')) :
    (X → Y) ≃ (occurrenceClass X ⟶ occurrenceClass Y) where
  toFun := occurrenceLiftHom
  invFun f x := (f.toFun (x, ⟨0, hn⟩)).1
  left_inv F := rfl
  right_inv f := by
    apply TokenClass.Hom.ext
    funext ⟨x, i⟩
    obtain ⟨y, hy⟩ := occurrenceClass_hom_apply f.toFun f.preserves x
    show (((f.toFun (x, ⟨0, hn⟩)).1 : Y), i) = f.toFun (x, i)
    rw [hy, hy]

theorem occurrenceLift_apply {D D' : Type u} {n : ℕ} (hn : 0 < n) (X : Set (Fin n → D))
    (Y : Set (Fin n → D')) (F : X → Y) :
    (occurrenceLift hn X Y F).toFun = occurrenceLiftFun F := rfl

/-- The correspondence preserves identities and composition. -/
theorem occurrenceLift_id {D : Type u} {n : ℕ} (hn : 0 < n) (X : Set (Fin n → D)) :
    occurrenceLift hn X X id = 𝟙 _ := rfl

theorem occurrenceLift_comp {D D' D'' : Type u} {n : ℕ} (hn : 0 < n) (X : Set (Fin n → D))
    (Y : Set (Fin n → D')) (Z : Set (Fin n → D'')) (F : X → Y) (G : Y → Z) :
    occurrenceLift hn X Z (G ∘ F) = occurrenceLift hn X Y F ≫ occurrenceLift hn Y Z G := rfl

/-! ### Canonical lexical transport (§9.2) -/

/-- A lossless tokenizer: a concatenation-preserving decoder `d : V^* → Γ^*` and a
deterministic encoder `τ` with `d ∘ τ = id`. -/
structure Tokenizer (Γ : Type u) where
  V : Type u
  d : FreeMonoid V →* FreeMonoid Γ
  τ : FreeMonoid Γ → FreeMonoid V
  d_τ : ∀ t, d (τ t) = t

namespace Tokenizer

variable {Γ : Type u} (T : Tokenizer Γ)

/-- Canonical sequences `C = im τ`. -/
def canonical : Set (FreeMonoid T.V) := Set.range T.τ

/-- `n = τ ∘ d`. -/
def normalize : FreeMonoid T.V → FreeMonoid T.V := T.τ ∘ T.d

theorem normalize_idempotent : T.normalize ∘ T.normalize = T.normalize := by
  funext s; simp [normalize, T.d_τ]

theorem normalize_fixed_iff (s : FreeMonoid T.V) : T.normalize s = s ↔ s ∈ T.canonical := by
  constructor
  · intro h; exact ⟨T.d s, h⟩
  · rintro ⟨t, rfl⟩; simp [normalize, T.d_τ]

/-- `s ⋆ t = τ(d(s) d(t))`, `e = τ(ε)`. -/
def star (s t : FreeMonoid T.V) : FreeMonoid T.V := T.τ (T.d s * T.d t)

/-- **Proposition 9.2** (part): `(C, ⋆, e)` is a monoid and `d|_C` is a monoid isomorphism
onto `Γ^*`. -/
@[instance_reducible] def canonicalMonoid : Monoid T.canonical where
  mul s t := ⟨T.star s t, ⟨_, rfl⟩⟩
  one := ⟨T.τ 1, ⟨1, rfl⟩⟩
  mul_assoc s t u := Subtype.ext <| by
    change T.star (T.star s.1 t.1) u.1 = T.star s.1 (T.star t.1 u.1)
    simp [star, T.d_τ, mul_assoc]
  one_mul := by
    rintro ⟨_, t, rfl⟩
    apply Subtype.ext
    change T.star (T.τ 1) (T.τ t) = T.τ t
    simp [star, T.d_τ]
  mul_one := by
    rintro ⟨_, t, rfl⟩
    apply Subtype.ext
    change T.star (T.τ t) (T.τ 1) = T.τ t
    simp [star, T.d_τ]

def canonicalIso : @MulEquiv T.canonical (FreeMonoid Γ) (T.canonicalMonoid).toMul _ :=
  letI := T.canonicalMonoid
  {
  toFun s := T.d s.1
  invFun t := ⟨T.τ t, t, rfl⟩
  left_inv := by
    rintro ⟨_, t, rfl⟩
    exact Subtype.ext (by simp [T.d_τ])
  right_inv t := T.d_τ t
  map_mul' s t := by
    change T.d (T.star s.1 t.1) = T.d s.1 * T.d t.1
    simp [star, T.d_τ] }

/-- The comparison `c_{ij} = τ_j ∘ d_i`. -/
def compare (T₁ T₂ : Tokenizer Γ) : FreeMonoid T₁.V → FreeMonoid T₂.V := T₂.τ ∘ T₁.d

/-- **Proposition 9.2** (part): `d_j ∘ c_{ij} = d_i`, `c_{jk} ∘ c_{ij} = c_{ik}`, `c_{ii} = n_i`. -/
theorem transport_identities (T₁ T₂ T₃ : Tokenizer Γ) :
    (∀ s, T₂.d (compare T₁ T₂ s) = T₁.d s) ∧
    (∀ s, compare T₂ T₃ (compare T₁ T₂ s) = compare T₁ T₃ s) ∧
    compare T₁ T₁ = T₁.normalize :=
  ⟨fun s => by simp [compare, T₂.d_τ], fun s => by simp [compare, T₂.d_τ], rfl⟩

/-- Restricted to canonical sequences, the comparisons are mutually inverse. -/
theorem compare_inverse (T₁ T₂ : Tokenizer Γ) (s : FreeMonoid T₁.V) (hs : s ∈ T₁.canonical) :
    compare T₂ T₁ (compare T₁ T₂ s) = s := by
  obtain ⟨t, rfl⟩ := hs
  simp [compare, T₁.d_τ, T₂.d_τ]

end Tokenizer

end AT

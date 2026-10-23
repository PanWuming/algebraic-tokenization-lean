import Mathlib

/-!
# Algebraic tokenization: basic definitions (paper §2.1)

* `AT.Word A E`  — the free monoid `F_E(A) = (A ⊔ E)^*`, realised as `List (A ⊕ E)`.
* `AT.wordMap f` — `F_E(f) = (f ⊔ id_E)^*`.
* `AT.TokenClass E` — a Token class `(A, E, H)` with heap `H ⊆ F_E(A)` (Definition 2.1).
* `AT.TokenClass.Hom` — a Token map: a carrier function `f` with `F_E(f)(H) ⊆ K`.
* The category instance `TS_E` and its carrier functor `AT.TokenClass.forget`.
-/

universe u v

namespace AT

open CategoryTheory

/-- `F_E(A) = (A ⊔ E)^*`. A word is a finite list of carrier values and core labels. -/
abbrev Word (A : Type u) (E : Type v) := List (A ⊕ E)

/-- `F_E(f) = (f ⊔ id_E)^*`: apply `f` entrywise, fix the core labels. -/
def wordMap {A B : Type u} {E : Type v} (f : A → B) : Word A E → Word B E :=
  List.map (Sum.map f id)

section wordMap
variable {A B C : Type u} {E : Type v}

@[simp] lemma wordMap_id : wordMap (E := E) (id : A → A) = id := by
  funext w; simp [wordMap, Sum.map_id_id]

lemma wordMap_comp (f : A → B) (g : B → C) :
    wordMap (E := E) (g ∘ f) = wordMap g ∘ wordMap f := by
  funext w; simp [wordMap, List.map_map, Sum.map_comp_map]

@[simp] lemma wordMap_nil (f : A → B) : wordMap (E := E) f [] = [] := rfl

@[simp] lemma wordMap_cons (f : A → B) (x : A ⊕ E) (w : Word A E) :
    wordMap f (x :: w) = Sum.map f id x :: wordMap f w := rfl

@[simp] lemma wordMap_append (f : A → B) (u v : Word A E) :
    wordMap f (u ++ v) = wordMap f u ++ wordMap f v := by
  simp [wordMap]

/-- Token maps preserve length (paper, after Definition 2.1). -/
@[simp] lemma length_wordMap (f : A → B) (w : Word A E) :
    (wordMap f w).length = w.length := by
  simp [wordMap]

/-- A word is core-only if it contains no carrier letter. -/
def CoreOnly (w : Word A E) : Prop := ∀ x ∈ w, Sum.isRight x = true

end wordMap

/-- A Token class `(A, E, H)` over a fixed core `E` (Definition 2.1). -/
structure TokenClass (E : Type v) where
  /-- The carrier `A`. -/
  carrier : Type u
  /-- The heap `H ⊆ F_E(A)`, the set of present records. -/
  heap : Set (Word carrier E)

namespace TokenClass

variable {E : Type v}

/-- A Token map `f : (A,E,H) → (B,E,K)`: a carrier function with `F_E(f)(H) ⊆ K`. -/
@[ext]
structure Hom (T₁ T₂ : TokenClass.{u} E) where
  toFun : T₁.carrier → T₂.carrier
  preserves : ∀ w ∈ T₁.heap, wordMap toFun w ∈ T₂.heap

/-- The Token Space category `TS_E`. -/
instance : Category (TokenClass.{u} E) where
  Hom := Hom
  id T := ⟨id, fun w hw => by simpa using hw⟩
  comp f g := ⟨g.toFun ∘ f.toFun, fun w hw => by
    rw [wordMap_comp]; exact g.preserves _ (f.preserves w hw)⟩

@[simp] lemma id_toFun (T : TokenClass.{u} E) : (𝟙 T : Hom T T).toFun = id := rfl
@[simp] lemma comp_toFun {T₁ T₂ T₃ : TokenClass.{u} E} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    (f ≫ g).toFun = g.toFun ∘ f.toFun := rfl

/-- The carrier functor `TS_E → Set`. Equality of Token maps is equality of the whole
carrier map, including its values on elements unused by the heap. -/
def forget : TokenClass.{u} E ⥤ Type u where
  obj T := T.carrier
  map f := TypeCat.ofHom f.toFun

@[simp] lemma forget_map {T₁ T₂ : TokenClass.{u} E} (f : T₁ ⟶ T₂) :
    (forget (E := E)).map f = TypeCat.ofHom f.toFun := rfl

instance : (forget (E := E)).Faithful where
  map_injective {X Y} f g h := Hom.ext (by
    have := congrArg (fun k : X.carrier ⟶ Y.carrier => (TypeCat.homEquiv k : _ → _)) h
    simpa [forget] using this)

/-- An empty heap permits every carrier function. -/
def homOfEmptyHeap {T₁ T₂ : TokenClass.{u} E} (h : T₁.heap = ∅)
    (f : T₁.carrier → T₂.carrier) : T₁ ⟶ T₂ :=
  ⟨f, fun w hw => by simp [h] at hw⟩

/-- `f` is (the carrier map of) a Token map `T₁ → T₂`. -/
def IsHom (T₁ T₂ : TokenClass.{u} E) (f : T₁.carrier → T₂.carrier) : Prop :=
  ∀ w ∈ T₁.heap, wordMap f w ∈ T₂.heap

/-- The set of carrier functions that are Token maps. -/
def admissible (T₁ T₂ : TokenClass.{u} E) : Set (T₁.carrier → T₂.carrier) :=
  {f | IsHom T₁ T₂ f}

@[simp] lemma mem_admissible {T₁ T₂ : TokenClass.{u} E} (f : T₁.carrier → T₂.carrier) :
    f ∈ admissible T₁ T₂ ↔ IsHom T₁ T₂ f := Iff.rfl

lemma admissible_eq_range_forget (T₁ T₂ : TokenClass.{u} E) :
    admissible T₁ T₂ = Set.range (fun f : T₁ ⟶ T₂ => f.toFun) := by
  ext f; constructor
  · intro hf; exact ⟨⟨f, hf⟩, rfl⟩
  · rintro ⟨g, rfl⟩; exact g.preserves

end TokenClass

end AT

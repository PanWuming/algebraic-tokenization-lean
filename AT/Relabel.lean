import AT.Signature

/-!
# Changing a signature and moving its parameters (paper §6)

* `AT.relabelWord α = q_A = (id_A ⊔ α)^*`.
* `AT.relabelPush α = α_!`, `AT.relabelPull α = α^*`; **Theorem 6.1** (`AT.relabelAdjunction`):
  `α_! ⊣ α^*`, fully faithful for injective `α`, not full in general.
* `AT.release` — the release functor `R_S : TS_{E ⊔ S} → TS_E`; **Example 6.2**;
  **Proposition 6.3** (controlled release and lifting).
* **Proposition 6.4** (adding term operations).
-/

universe u v w

namespace AT

open CategoryTheory

variable {E E' : Type v}

/-- `q_A = (id_A ⊔ α)^* : F_E(A) → F_{E'}(A)`. -/
def relabelWord {A : Type u} {E' : Type w} (α : E → E') : Word A E → Word A E' := List.map (Sum.map id α)

/-- The naturality square `q_B ∘ F_E(f) = F_{E'}(f) ∘ q_A` (Figure 4). -/
theorem relabelWord_wordMap {A B : Type u} {E' : Type w} (α : E → E') (f : A → B) (w : Word A E) :
    relabelWord α (wordMap f w) = wordMap f (relabelWord α w) := by
  simp [relabelWord, wordMap, List.map_map, Function.comp_def, Sum.map_map]

/-- `α_!(A,E,H) = (A, E', q_A(H))`. -/
def relabelPush (α : E → E') : TokenClass.{u} E ⥤ TokenClass.{u} E' where
  obj T := ⟨T.carrier, relabelWord α '' T.heap⟩
  map f := ⟨f.toFun, by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨_, f.preserves w hw, relabelWord_wordMap α _ w⟩⟩

/-- `α^*(B,E',K) = (B, E, q_B⁻¹(K))`. -/
def relabelPull (α : E → E') : TokenClass.{u} E' ⥤ TokenClass.{u} E where
  obj T := ⟨T.carrier, relabelWord α ⁻¹' T.heap⟩
  map {X Y} f := ⟨f.toFun, fun w hw => by
    show relabelWord α (wordMap f.toFun w) ∈ Y.heap
    rw [relabelWord_wordMap]; exact f.preserves _ hw⟩

lemma relabelWord_injective {A : Type u} {E' : Type w} {α : E → E'} (hα : Function.Injective α) :
    Function.Injective (relabelWord (A := A) α) :=
  List.map_injective_iff.mpr (Sum.map_injective.mpr ⟨Function.injective_id, hα⟩)

/-- **Theorem 6.1** (core relabeling): `α_! ⊣ α^*`. -/
def relabelAdjunction (α : E → E') : relabelPush.{u} α ⊣ relabelPull α :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun g => ⟨g.toFun, fun w hw => by
            show relabelWord α (wordMap g.toFun w) ∈ Y.heap
            rw [relabelWord_wordMap α g.toFun w]; exact g.preserves _ ⟨w, hw, rfl⟩⟩
          invFun := fun g => ⟨g.toFun, by
            rintro _ ⟨w, hw, rfl⟩
            erw [← relabelWord_wordMap α g.toFun w]; exact g.preserves w hw⟩
          left_inv := fun g => rfl
          right_inv := fun g => rfl }
      homEquiv_naturality_left_symm := fun _ _ => rfl
      homEquiv_naturality_right := fun _ _ => rfl }

/-- **Theorem 6.1**: if `α` is injective, `α_!` is fully faithful. -/
theorem relabelPush_full_of_injective (α : E → E') (hα : Function.Injective α) :
    (relabelPush.{u} α).Full ∧ (relabelPush.{u} α).Faithful := by
  refine ⟨⟨fun {X Y} g => ?_⟩, ⟨fun {X Y} f g h => ?_⟩⟩
  · refine ⟨⟨g.toFun, fun w hw => ?_⟩, rfl⟩
    obtain ⟨v, hv, hvw⟩ := g.preserves _ ⟨w, hw, rfl⟩
    erw [← relabelWord_wordMap α g.toFun w] at hvw
    have hv' := relabelWord_injective hα hvw
    exact hv' ▸ hv
  · exact TokenClass.Hom.ext (congrArg TokenClass.Hom.toFun h :)

/-- **Theorem 6.1**: if `α` is not injective, `α_!` need not be full. Witness: heaps
`{(e₀,a)}` and `{(e₁,b)}` on singletons with `α e₀ = α e₁`. -/
theorem relabelPush_not_full_of_not_injective :
    ∃ (α : Bool → Unit), ¬ (relabelPush.{0} α).Full := by
  refine ⟨fun _ => (), fun hF => ?_⟩
  let X : TokenClass.{0} Bool := ⟨Unit, {[Sum.inr false, Sum.inl ()]}⟩
  let Y : TokenClass.{0} Bool := ⟨Unit, {[Sum.inr true, Sum.inl ()]}⟩
  let g : (relabelPush (fun _ : Bool => ())).obj X ⟶ (relabelPush (fun _ : Bool => ())).obj Y :=
    ⟨id, by
      rintro _ ⟨v, hv, rfl⟩
      rw [Set.mem_singleton_iff] at hv
      subst hv
      exact ⟨_, Set.mem_singleton _, rfl⟩⟩
  obtain ⟨f, -⟩ := hF.map_surjective g
  have := f.preserves _ (Set.mem_singleton _)
  simp [Y, wordMap] at this

/-! ### Release (§6.2) -/

variable (S : Type v)

/-- Retag a word over core `E ⊔ S` on carrier `A` as a word over core `E` on carrier `A ⊔ S`. -/
def releaseWord {A : Type v} : Word A (E ⊕ S) → Word (A ⊕ S) E
  | [] => []
  | Sum.inl a :: w => Sum.inl (Sum.inl a) :: releaseWord w
  | Sum.inr (Sum.inl e) :: w => Sum.inr e :: releaseWord w
  | Sum.inr (Sum.inr s) :: w => Sum.inl (Sum.inr s) :: releaseWord w

/-- The release functor `R_S : TS_{E ⊔ S} → TS_E`, `f ↦ f ⊔ id_S`. -/
lemma releaseWord_wordMap {A B : Type v} (f : A → B) (w : Word A (E ⊕ S)) :
    releaseWord S (wordMap f w) = wordMap (Sum.map f id) (releaseWord S w) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rcases x with a | e | s <;> simp [releaseWord, ih]

lemma releaseWord_injective {A : Type v} : Function.Injective (releaseWord (E := E) S (A := A)) := by
  intro u v h
  induction u generalizing v with
  | nil =>
    rcases v with _ | ⟨x, v⟩
    · rfl
    · rcases x with a | e | s <;> simp [releaseWord] at h
  | cons x u ih =>
    rcases v with _ | ⟨y, v⟩
    · rcases x with a | e | s <;> simp [releaseWord] at h
    · rcases x with a | e | s <;> rcases y with b | e' | s' <;> simp [releaseWord] at h <;>
        simp [h.1, ih h.2]

def release : TokenClass.{v} (E ⊕ S) ⥤ TokenClass.{v} E where
  obj T := ⟨T.carrier ⊕ S, releaseWord S '' T.heap⟩
  map f := ⟨Sum.map f.toFun id, by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨_, f.preserves w hw, releaseWord_wordMap S _ w⟩⟩
  map_comp f g := TokenClass.Hom.ext (funext fun x => by cases x <;> rfl)

lemma sumMap_id_injective {A B : Type v} :
    Function.Injective (fun f : A → B => Sum.map f (id : S → S)) := by
  intro f g h
  funext a
  simpa using congrFun h (Sum.inl a)

instance release_faithful : (release.{v} (E := E) S).Faithful where
  map_injective h :=
    TokenClass.Hom.ext (sumMap_id_injective S (congrArg TokenClass.Hom.toFun h :))

/-- **Example 6.2**: `E = ∅`, `S = {s}`, `A = {a}`, empty heap: the source has one
endomorphism, its release has four. -/
theorem release_example :
    let T : TokenClass.{0} (PEmpty ⊕ Unit) := ⟨Unit, ∅⟩
    Nonempty (Unique (T ⟶ T)) ∧ Nat.card ((release Unit).obj T ⟶ (release Unit).obj T) = 4 := by
  intro T
  refine ⟨⟨⟨⟨𝟙 T⟩, fun f => TokenClass.Hom.ext (funext fun _ => rfl)⟩⟩, ?_⟩
  have hT : ((release Unit).obj T).heap = ∅ := by
    show releaseWord Unit '' (∅ : Set (Word Unit (PEmpty ⊕ Unit))) = ∅
    simp
  let e : ((release Unit).obj T ⟶ (release Unit).obj T) ≃ (Unit ⊕ Unit → Unit ⊕ Unit) :=
    { toFun := fun f => f.toFun
      invFun := fun f => TokenClass.homOfEmptyHeap hT f
      left_inv := fun f => TokenClass.Hom.ext rfl
      right_inv := fun f => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  simp

/-- The category `D_{E,S}` with a designated decomposition `A ⊔ S` and arrows `f ⊔ id_S`. -/
structure Decomposed where
  base : TokenClass.{v} (E ⊕ S)

instance : Category (Decomposed (E := E) S) where
  Hom X Y := {g : (release S).obj X.base ⟶ (release S).obj Y.base //
    ∃ f : X.base.carrier → Y.base.carrier, g.toFun = Sum.map f id}
  id X := ⟨𝟙 _, id, Sum.map_id_id.symm⟩
  comp f g := ⟨f.1 ≫ g.1, by
    obtain ⟨f₀, hf⟩ := f.2
    obtain ⟨g₀, hg⟩ := g.2
    exact ⟨g₀ ∘ f₀, by rw [TokenClass.comp_toFun, hf, hg]; funext x; cases x <;> rfl⟩⟩

/-- The retagging functor `TS_{E ⊔ S} → D_{E,S}`. -/
def toDecomposed : TokenClass.{v} (E ⊕ S) ⥤ Decomposed (E := E) S where
  obj T := ⟨T⟩
  map f := ⟨(release S).map f, f.toFun, rfl⟩

instance toDecomposed_full : (toDecomposed (E := E) S).Full where
  map_surjective {X Y} g := by
    obtain ⟨f, hf⟩ := g.2
    refine ⟨⟨f, fun w hw => ?_⟩, ?_⟩
    · obtain ⟨v, hv, hvw⟩ := g.1.preserves _ ⟨w, hw, rfl⟩
      rw [hf] at hvw; erw [← releaseWord_wordMap S f w] at hvw
      have hv' := releaseWord_injective S hvw
      exact hv' ▸ hv
    · exact Subtype.ext (TokenClass.Hom.ext hf.symm)

instance toDecomposed_faithful : (toDecomposed (E := E) S).Faithful where
  map_injective h :=
    TokenClass.Hom.ext (sumMap_id_injective S (congrArg (fun k => k.1.toFun) h :))

instance toDecomposed_essSurj : (toDecomposed (E := E) S).EssSurj where
  mem_essImage X := ⟨X.base, ⟨Iso.refl _⟩⟩

instance toDecomposed_isEquivalence : (toDecomposed (E := E) S).IsEquivalence where

/-- **Proposition 6.3**: retagging gives an equivalence `TS_{E ⊔ S} ≌ D_{E,S}`. -/
noncomputable def release_equiv : TokenClass.{v} (E ⊕ S) ≌ Decomposed (E := E) S :=
  (toDecomposed S).asEquivalence

/-- The forgetful functor `D_{E,S} → TS_E`. -/
def Decomposed.forget : Decomposed (E := E) S ⥤ TokenClass.{v} E where
  obj X := (release S).obj X.base
  map f := f.1

instance : (Decomposed.forget (E := E) S).Faithful where
  map_injective h := Subtype.ext h

/-- **Proposition 6.3**: the forgetful functor need not be full. -/
theorem Decomposed.forget_not_full : ¬ (Decomposed.forget (E := PEmpty) Unit).Full := by
  intro hF
  let X : Decomposed (E := PEmpty) Unit := ⟨⟨Unit, ∅⟩⟩
  have hX : ((release Unit).obj X.base).heap = ∅ := by
    show releaseWord Unit '' (∅ : Set (Word Unit (PEmpty ⊕ Unit))) = ∅
    simp
  let g : (Decomposed.forget Unit).obj X ⟶ (Decomposed.forget Unit).obj X :=
    TokenClass.homOfEmptyHeap hX Sum.swap
  obtain ⟨⟨h, f, hf⟩, rfl⟩ := hF.map_surjective g
  have := congrFun hf (Sum.inr ())
  simp [Decomposed.forget, g, TokenClass.homOfEmptyHeap] at this

/-! ### Naming and definitional expansion (§6.3) -/

/-- Expansion by naming: adjoin fresh labels `ṡ` and records `(ṡ, j_A(s))`. -/
abbrev nameValues {T : TokenClass.{u} E} {S : Type w} (j : S → T.carrier) : TokenClass.{u} (E ⊕ S) :=
  ⟨T.carrier, relabelWord Sum.inl '' T.heap ∪ {w | ∃ s, w = [Sum.inr (Sum.inr s), Sum.inl (j s)]}⟩

/-- A Token map between named expansions is exactly an original Token map with `f ∘ j_A = j_B`. -/
theorem nameValues_hom_iff {T₁ T₂ : TokenClass.{u} E} {S : Type w}
    (j₁ : S → T₁.carrier) (j₂ : S → T₂.carrier) (f : T₁.carrier → T₂.carrier) :
    TokenClass.IsHom (nameValues j₁) (nameValues j₂) f ↔
      TokenClass.IsHom T₁ T₂ f ∧ f ∘ j₁ = j₂ := by
  have hrec : ∀ {A : Type u} (u : Word A E) (s : S), Sum.inr (Sum.inr s) ∉ relabelWord Sum.inl u := by
    intro A u s h
    simp only [relabelWord, List.mem_map] at h
    obtain ⟨x, -, hx⟩ := h
    rcases x with a | e <;> simp at hx
  constructor
  · intro hf
    refine ⟨fun w hw => ?_, funext fun s => ?_⟩
    · rcases hf _ (Or.inl ⟨w, hw, rfl⟩) with ⟨v, hv, hvw⟩ | ⟨s, hs⟩
      · rw [← relabelWord_wordMap] at hvw
        rwa [← relabelWord_injective Sum.inl_injective hvw]
      · rw [← relabelWord_wordMap Sum.inl f w] at hs
        exact absurd (by rw [hs]; simp) (hrec _ s)
    · rcases hf _ (Or.inr ⟨s, rfl⟩) with ⟨v, -, hv⟩ | ⟨s', hs'⟩
      · exact absurd (by rw [hv]; simp [wordMap]) (hrec v s)
      · simp [wordMap] at hs'
        obtain ⟨rfl, h⟩ := hs'
        exact h
  · rintro ⟨hf, hj⟩ w (⟨v, hv, rfl⟩ | ⟨s, rfl⟩)
    · exact Or.inl ⟨_, hf v hv, relabelWord_wordMap Sum.inl f v⟩
    · refine Or.inr ⟨s, ?_⟩
      simp [wordMap, ← hj]

/-- A `Sg`-term with variables in `Fin n`. -/
inductive Term (Sg : AlgSig.{v}) (n : ℕ) : Type v
  | var : Fin n → Term Sg n
  | app : (ω : Sg.opSymbols) → (Fin (Sg.opArity ω) → Term Sg n) → Term Sg n

/-- Evaluate a term in a structure. -/
def Term.eval {Sg : AlgSig.{v}} {n : ℕ} (X : Str.{u} Sg) (v : Fin n → X.carrier) : Term Sg n → X.carrier
  | .var i => v i
  | .app ω ts => X.op ω fun i => (ts i).eval X v

/-- Homomorphisms preserve term operations. -/
theorem Term.eval_hom {Sg : AlgSig.{v}} {n : ℕ} {X Y : Str.{u} Sg} (f : X ⟶ Y) (v : Fin n → X.carrier)
    (t : Term Sg n) : f.toFun (t.eval X v) = t.eval Y (f.toFun ∘ v) := by
  induction t with
  | var i => rfl
  | app ω ts ih =>
    simp only [Term.eval, f.map_op]
    congr 1
    funext i
    exact ih i

/-- The expanded signature with new operation symbols indexed by `ι`. -/
def AlgSig.addOps (Sg : AlgSig.{v}) (ι : Type v) (ar : ι → ℕ) : AlgSig.{v} :=
  ⟨Sg.relSymbols, Sg.relArity, Sg.opSymbols ⊕ ι, Sum.elim Sg.opArity ar⟩

/-- Canonical expansion: interpret each new symbol by a fixed term. -/
def Str.expandByTerms {Sg : AlgSig.{v}} {ι : Type v} {ar : ι → ℕ} (τ : ∀ i, Term Sg (ar i))
    (X : Str.{u} Sg) : Str.{u} (Sg.addOps ι ar) :=
  ⟨X.carrier, X.rel, fun ω => match ω with
    | Sum.inl ω => X.op ω
    | Sum.inr i => fun a => (τ i).eval X a⟩

/-- The expansion functor. -/
def expandByTerms {Sg : AlgSig.{v}} {ι : Type v} {ar : ι → ℕ} (τ : ∀ i, Term Sg (ar i)) :
    Str.{u} Sg ⥤ Str.{u} (Sg.addOps ι ar) where
  obj := Str.expandByTerms τ
  map f := ⟨f.toFun, f.preserves_rel, by
    rintro (ω | i) a
    · exact f.map_op ω a
    · exact Term.eval_hom f a (τ i)⟩

/-- **Proposition 6.4** (adding term operations): the expansion functor is fully faithful, and
the tokenized version admits exactly the same carrier maps. -/
theorem expandByTerms_fullyFaithful {Sg : AlgSig.{v}} {ι : Type v} {ar : ι → ℕ} (τ : ∀ i, Term Sg (ar i)) :
    (expandByTerms.{u} τ).Full ∧ (expandByTerms.{u} τ).Faithful := by
  refine ⟨⟨fun {X Y} g => ⟨⟨g.toFun, g.preserves_rel, fun ω a => g.map_op (Sum.inl ω) a⟩, rfl⟩⟩,
    ⟨fun h => Str.Hom.ext (congrArg Str.Hom.toFun h :)⟩⟩

end AT

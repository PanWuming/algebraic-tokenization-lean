import AT.Shape

/-!
# Algebraic signatures, relationalization and the algebraic image (paper §2.3, §3)

* `AT.AlgSig` — a signature with relation and operation symbols (Definition 2.5).
* `AT.Str Sg` — structures interpreting operations as total functions; the category `Str(Sg)`.
* `AT.Rep` — the tokenization functor `Str(Sg) → TS_{E_Sg}` (eq. 2.5); **Proposition 2.6**: fully faithful.
* **Theorem 3.2** (exact algebraic image), **Proposition 3.3** (location of finite limits),
  **Example 3.4** (a relational exponential loses totality),
  **Theorem 3.5** (the quotient criterion), **Example 3.6**.
-/

universe u v

namespace AT

open CategoryTheory

/-- A signature with disjoint relation and operation symbol sets and finite arities;
constants are zero-ary operations (Definition 2.5). -/
structure AlgSig where
  relSymbols : Type v
  relArity : relSymbols → ℕ
  opSymbols : Type v
  opArity : opSymbols → ℕ

namespace AlgSig

variable (Sg : AlgSig.{v})

/-- The core `E_Sg`: one distinct label per symbol. -/
abbrev core := Sg.relSymbols ⊕ Sg.opSymbols

/-- The shape `(R, □, …, □)` of an `n`-ary relation symbol. -/
def relShape (R : Sg.relSymbols) : Shape.{u} Sg.core :=
  Sum.inr (Sum.inl R) :: List.replicate (Sg.relArity R) (Sum.inl PUnit.unit)

/-- The graph shape `(ω, □, …, □, □)` of a `k`-ary operation symbol. -/
def opShape (ω : Sg.opSymbols) : Shape.{u} Sg.core :=
  Sum.inr (Sum.inr ω) :: List.replicate (Sg.opArity ω + 1) (Sum.inl PUnit.unit)

/-- `L_Sg`: the shapes of the signature. -/
def shapes : Set (Shape.{u} Sg.core) :=
  Set.range Sg.relShape ∪ Set.range Sg.opShape

end AlgSig

/-- A `Sg`-structure with total operations. -/
structure Str (Sg : AlgSig.{v}) where
  carrier : Type u
  rel : ∀ R : Sg.relSymbols, Set (Fin (Sg.relArity R) → carrier)
  op : ∀ ω : Sg.opSymbols, (Fin (Sg.opArity ω) → carrier) → carrier

namespace Str

variable {Sg : AlgSig.{v}}

/-- Homomorphisms of structures: preserve relations, commute with operations. -/
@[ext]
structure Hom (X Y : Str.{u} Sg) where
  toFun : X.carrier → Y.carrier
  preserves_rel : ∀ R a, a ∈ X.rel R → toFun ∘ a ∈ Y.rel R
  map_op : ∀ ω a, toFun (X.op ω a) = Y.op ω (toFun ∘ a)

/-- The category `Str(Sg)`. -/
instance : Category (Str.{u} Sg) where
  Hom := Hom
  id X := ⟨id, fun _ _ h => h, fun _ _ => rfl⟩
  comp f g := ⟨g.toFun ∘ f.toFun, fun R a h => g.preserves_rel R _ (f.preserves_rel R a h),
    fun ω a => by simp [Function.comp_apply, f.map_op, g.map_op, Function.comp_assoc]⟩

def forget : Str.{u} Sg ⥤ Type u where
  obj X := X.carrier
  map f := TypeCat.ofHom f.toFun

/-- A record `(R, a)` for a relation instance. -/
def relRecord (X : Str.{u} Sg) (R : Sg.relSymbols) (a : Fin (Sg.relArity R) → X.carrier) :
    Word X.carrier Sg.core :=
  Sum.inr (Sum.inl R) :: (List.ofFn a).map Sum.inl

/-- A record `(ω, a, ω^X(a))` for an operation instance. -/
def opRecord (X : Str.{u} Sg) (ω : Sg.opSymbols) (a : Fin (Sg.opArity ω) → X.carrier) :
    Word X.carrier Sg.core :=
  Sum.inr (Sum.inr ω) :: ((List.ofFn a).map Sum.inl ++ [Sum.inl (X.op ω a)])

/-- The heap `H_X` of eq. (2.5). -/
def heap (X : Str.{u} Sg) : Set (Word X.carrier Sg.core) :=
  {w | ∃ R a, a ∈ X.rel R ∧ w = X.relRecord R a} ∪ {w | ∃ ω a, w = X.opRecord ω a}

/-- The word `(ω, a, b)`: an operation-shaped record with an arbitrary output `b`. -/
def opWord {A : Type u} (ω : Sg.opSymbols) (a : Fin (Sg.opArity ω) → A) (b : A) :
    Word A Sg.core :=
  Sum.inr (Sum.inr ω) :: ((List.ofFn a).map Sum.inl ++ [Sum.inl b])

lemma opRecord_eq (X : Str.{u} Sg) (ω : Sg.opSymbols) (a : Fin (Sg.opArity ω) → X.carrier) :
    X.opRecord ω a = opWord ω a (X.op ω a) := rfl

lemma wordMap_relRecord {X : Str.{u} Sg} {B : Type u} (f : X.carrier → B) (R : Sg.relSymbols)
    (a : Fin (Sg.relArity R) → X.carrier) :
    wordMap f (X.relRecord R a) =
      Sum.inr (Sum.inl R) :: (List.ofFn (f ∘ a)).map Sum.inl := by
  simp [relRecord, wordMap, List.map_ofFn, Function.comp_def]

lemma wordMap_opWord {A B : Type u} (f : A → B) (ω : Sg.opSymbols) (a : Fin (Sg.opArity ω) → A)
    (b : A) : wordMap f (opWord ω a b) = opWord ω (f ∘ a) (f b) := by
  simp [opWord, wordMap, List.map_ofFn, Function.comp_def]

lemma wordMap_opRecord {X : Str.{u} Sg} {B : Type u} (f : X.carrier → B) (ω : Sg.opSymbols)
    (a : Fin (Sg.opArity ω) → X.carrier) :
    wordMap f (X.opRecord ω a) = opWord ω (f ∘ a) (f (X.op ω a)) :=
  wordMap_opWord f ω a _

lemma relRecord_injective {A : Type u} (R : Sg.relSymbols) {a a' : Fin (Sg.relArity R) → A} :
    (Sum.inr (Sum.inl R) :: (List.ofFn a).map Sum.inl : Word A Sg.core) =
      Sum.inr (Sum.inl R) :: (List.ofFn a').map Sum.inl → a = a' := by
  intro h
  have h1 := List.cons.inj h
  exact List.ofFn_inj.mp (List.map_injective_iff.mpr Sum.inl_injective h1.2)

lemma opWord_inj {A : Type u} {ω : Sg.opSymbols} {a a' : Fin (Sg.opArity ω) → A} {b b' : A}
    (h : opWord ω a b = opWord ω a' b') : a = a' ∧ b = b' := by
  have h1 := (List.cons.inj h).2
  refine ⟨List.ofFn_inj.mp (List.map_injective_iff.mpr Sum.inl_injective
    (List.append_inj_left' h1 rfl)), ?_⟩
  simpa using List.append_inj_right' h1 rfl

lemma opWord_symbol_eq {A : Type u} {ω ω' : Sg.opSymbols} {a : Fin (Sg.opArity ω) → A}
    {a' : Fin (Sg.opArity ω') → A} {b b' : A} (h : opWord ω a b = opWord ω' a' b') : ω = ω' := by
  simpa [opWord] using (List.cons.inj h).1

lemma relRecord_mem_heap_iff (X : Str.{u} Sg) (R : Sg.relSymbols)
    (a : Fin (Sg.relArity R) → X.carrier) : X.relRecord R a ∈ X.heap ↔ a ∈ X.rel R := by
  constructor
  · rintro (⟨R', a', ha', h⟩ | ⟨ω, a', h⟩)
    · have hR : R = R' := by simpa [relRecord] using (List.cons.inj h).1
      subst hR
      rwa [relRecord_injective R h]
    · simp [relRecord, opRecord] at h
  · intro h; exact Or.inl ⟨R, a, h, rfl⟩

lemma opWord_mem_heap_iff (X : Str.{u} Sg) (ω : Sg.opSymbols) (a : Fin (Sg.opArity ω) → X.carrier)
    (b : X.carrier) : opWord ω a b ∈ X.heap ↔ b = X.op ω a := by
  constructor
  · rintro (⟨R, a', _, h⟩ | ⟨ω', a', h⟩)
    · simp [relRecord, opWord] at h
    · rw [opRecord_eq] at h
      have hω := opWord_symbol_eq h
      subst hω
      obtain ⟨rfl, rfl⟩ := opWord_inj h
      rfl
  · rintro rfl; exact Or.inr ⟨ω, a, rfl⟩

lemma opRecord_mem_heap (X : Str.{u} Sg) (ω : Sg.opSymbols) (a : Fin (Sg.opArity ω) → X.carrier) :
    X.opRecord ω a ∈ X.heap := Or.inr ⟨ω, a, rfl⟩

lemma nil_notMem_heap (X : Str.{u} Sg) : ([] : Word X.carrier Sg.core) ∉ X.heap := by
  rintro (⟨R, a, _, h⟩ | ⟨ω, a, h⟩) <;> simp [relRecord, opRecord] at h

/-- The heap of a structure is preserved by homomorphisms. -/
lemma Hom.preserves_heap {X Y : Str.{u} Sg} (f : X ⟶ Y) :
    ∀ w ∈ X.heap, wordMap f.toFun w ∈ Y.heap := by
  rintro w (⟨R, a, ha, rfl⟩ | ⟨ω, a, rfl⟩)
  · rw [wordMap_relRecord]; exact Or.inl ⟨R, _, f.preserves_rel R a ha, rfl⟩
  · rw [wordMap_opRecord, f.map_op]; exact Or.inr ⟨ω, _, rfl⟩

end Str

section lift

variable {A B : Type u} {E : Type v}

/-- Lifting a word of carrier entries along `f`. -/
lemma exists_of_wordMap_eq_map_inl (f : A → B) :
    ∀ {n : ℕ} (w : Word A E) (b : Fin n → B), wordMap f w = (List.ofFn b).map Sum.inl →
      ∃ a : Fin n → A, w = (List.ofFn a).map Sum.inl ∧ f ∘ a = b
  | 0, w, b, h => by
    refine ⟨Fin.elim0, ?_, funext fun i => i.elim0⟩
    simpa [wordMap] using h
  | n + 1, [], b, h => by simp [List.ofFn_succ] at h
  | n + 1, x :: w, b, h => by
    rw [List.ofFn_succ, List.map_cons, wordMap_cons] at h
    obtain ⟨hx, hw⟩ := List.cons.inj h
    rcases x with a₀ | e
    · obtain ⟨a, rfl, ha⟩ := exists_of_wordMap_eq_map_inl f w (fun i => b i.succ) hw
      refine ⟨Fin.cons a₀ a, ?_, ?_⟩
      · simp [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
      · rw [Fin.comp_cons, ha]
        exact (Fin.cons_self_tail b).symm ▸ by
          congr 1; simpa using hx
    · simp at hx

lemma exists_of_wordMap_eq_cons (f : A → B) {n : ℕ} (w : Word A E) (e : E) (b : Fin n → B)
    (h : wordMap f w = Sum.inr e :: (List.ofFn b).map Sum.inl) :
    ∃ a : Fin n → A, w = Sum.inr e :: (List.ofFn a).map Sum.inl ∧ f ∘ a = b := by
  rcases w with _ | ⟨x, w⟩
  · simp at h
  · rw [wordMap_cons] at h
    obtain ⟨hx, hw⟩ := List.cons.inj h
    rcases x with a | e'
    · simp at hx
    · obtain rfl : e' = e := by simpa using hx
      obtain ⟨a, rfl, ha⟩ := exists_of_wordMap_eq_map_inl f w b hw
      exact ⟨a, rfl, ha⟩

lemma wordMap_inr_cons_map_inl (f : A → B) {n : ℕ} (e : E) (a : Fin n → A) :
    wordMap f (Sum.inr e :: (List.ofFn a).map Sum.inl) =
      Sum.inr e :: (List.ofFn (f ∘ a)).map Sum.inl := by
  simp [wordMap, List.map_ofFn, Function.comp_def]

/-- `(ofFn a).map inl ++ [inl b]` is `(ofFn (snoc a b)).map inl`. -/
lemma map_inl_ofFn_snoc {n : ℕ} (a : Fin n → A) (b : A) :
    ((List.ofFn (Fin.snoc a b : Fin (n + 1) → A)).map Sum.inl : Word A E) =
      (List.ofFn a).map Sum.inl ++ [Sum.inl b] := by
  rw [List.ofFn_succ', List.concat_eq_append, List.map_append]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

end lift

/-- The tokenization functor `Rep : Str(Sg) → TS_{E_Sg}` (eq. 2.5). -/
def Rep (Sg : AlgSig.{v}) : Str.{u} Sg ⥤ TokenClass.{u} Sg.core where
  obj X := ⟨X.carrier, X.heap⟩
  map f := ⟨f.toFun, f.preserves_heap⟩

@[simp] lemma Rep_obj_carrier {Sg : AlgSig.{v}} (X : Str.{u} Sg) :
    ((Rep Sg).obj X).carrier = X.carrier := rfl
@[simp] lemma Rep_obj_heap {Sg : AlgSig.{v}} (X : Str.{u} Sg) :
    ((Rep Sg).obj X).heap = X.heap := rfl
@[simp] lemma Rep_map_toFun {Sg : AlgSig.{v}} {X Y : Str.{u} Sg} (f : X ⟶ Y) :
    ((Rep Sg).map f).toFun = f.toFun := rfl

/-- A purely relational signature as an algebraic signature with no operation symbols. -/
def RelSig.toAlgSig (Sg : RelSig.{v}) : AlgSig.{v} where
  relSymbols := Sg.symbols
  relArity := Sg.arity
  opSymbols := PEmpty
  opArity := PEmpty.elim

/-- A relational structure as a `Sg.toAlgSig`-structure. -/
def RelStr.toStr {Sg : RelSig.{v}} (X : RelStr.{u} Sg) : Str.{u} Sg.toAlgSig where
  carrier := X.carrier
  rel := X.rel
  op ω := ω.elim

/-- `Rel(Sg) → Str(Sg.toAlgSig)` (an isomorphism of categories). -/
def RelStr.toStrFunctor (Sg : RelSig.{v}) : RelStr.{u} Sg ⥤ Str.{u} Sg.toAlgSig where
  obj := RelStr.toStr
  map f := ⟨f.toFun, f.preserves, fun ω _ => ω.elim⟩

/-- The tokenization of relational structures `Rep : Rel(Sg) → TS_{E_Sg}`. -/
def relRep (Sg : RelSig.{v}) : RelStr.{u} Sg ⥤ TokenClass.{u} Sg.toAlgSig.core :=
  RelStr.toStrFunctor Sg ⋙ Rep Sg.toAlgSig

/-- **Proposition 2.6** (relationalization): `Rep` is fully faithful. -/
instance Rep_full (Sg : AlgSig.{v}) : (Rep.{u} Sg).Full where
  map_surjective {X Y} g :=
    ⟨⟨g.toFun,
      fun R a ha => by
        have h1 := g.preserves _ ((X.relRecord_mem_heap_iff R a).mpr ha)
        have h2 : wordMap g.toFun (X.relRecord R a) = Y.relRecord R (g.toFun ∘ a) :=
          Str.wordMap_relRecord _ R a
        exact (Y.relRecord_mem_heap_iff R _).mp
          ((congrArg (· ∈ ((Rep Sg).obj Y).heap) h2).mp h1),
      fun ω a => by
        have h1 := g.preserves _ (X.opRecord_mem_heap ω a)
        have h2 : wordMap g.toFun (X.opRecord ω a) = Str.opWord ω (g.toFun ∘ a) (g.toFun (X.op ω a)) :=
          Str.wordMap_opRecord _ ω a
        exact (Y.opWord_mem_heap_iff ω _ _).mp
          ((congrArg (· ∈ ((Rep Sg).obj Y).heap) h2).mp h1)⟩,
      TokenClass.Hom.ext rfl⟩

instance Rep_faithful (Sg : AlgSig.{v}) : (Rep.{u} Sg).Faithful where
  map_injective h := Str.Hom.ext (by simpa [Rep] using congrArg TokenClass.Hom.toFun h)

/-- `Rep` retains carriers and underlying functions. -/
theorem Rep_forget (Sg : AlgSig.{v}) : Rep.{u} Sg ⋙ TokenClass.forget = Str.forget := by
  rfl

/-- The restriction of `Rep` to any full subcategory remains fully faithful. -/
theorem Rep_restrict_full (Sg : AlgSig.{v}) (P : ObjectProperty (Str.{u} Sg)) :
    (P.ι ⋙ Rep.{u} Sg).Full ∧ (P.ι ⋙ Rep.{u} Sg).Faithful :=
  ⟨inferInstance, inferInstance⟩

/-! ### The algebraic image (§3.1) -/

/-- The condition of **Theorem 3.2**: every record has a shape in `L_Sg`, and every operation
shape is the graph of a total function. -/
def TokenClass.IsAlgebraic {Sg : AlgSig.{v}} (T : TokenClass.{u} Sg.core) : Prop :=
  (∀ w ∈ T.heap, shape w ∈ Sg.shapes) ∧
  ∀ (ω : Sg.opSymbols) (a : Fin (Sg.opArity ω) → T.carrier),
    ∃! b, (Sum.inr (Sum.inr ω) :: ((List.ofFn a).map Sum.inl ++ [Sum.inl b])) ∈ T.heap

/-- **Theorem 3.2** (exact algebraic image): `T` is the tokenization of a `Sg`-structure
exactly when it is algebraic, and the structure is then unique. -/
theorem Rep_image_iff {Sg : AlgSig.{v}} (T : TokenClass.{u} Sg.core) :
    (∃ X : Str.{u} Sg, (Rep Sg).obj X = T) ↔ T.IsAlgebraic := by
  constructor
  · rintro ⟨X, rfl⟩
    refine ⟨?_, fun ω a => ?_⟩
    · rintro w (⟨R, a, _, rfl⟩ | ⟨ω, a, rfl⟩)
      · exact Or.inl ⟨R, by simp [shape, wordMap, Str.relRecord, AlgSig.relShape,
          List.map_ofFn, Function.comp_def, List.ofFn_const]⟩
      · exact Or.inr ⟨ω, by simp [shape, wordMap, Str.opRecord, AlgSig.opShape,
          List.map_ofFn, Function.comp_def, List.ofFn_const, List.replicate_succ']⟩
    · refine ⟨X.op ω a, (X.opWord_mem_heap_iff ω a _).mpr rfl, fun b hb => ?_⟩
      exact (X.opWord_mem_heap_iff ω a b).mp hb
  · rintro ⟨hshape, hop⟩
    let X : Str.{u} Sg :=
      { carrier := T.carrier
        rel := fun R => {a | (Sum.inr (Sum.inl R) :: (List.ofFn a).map Sum.inl) ∈ T.heap}
        op := fun ω a => (hop ω a).exists.choose }
    have hopX : ∀ ω a, Str.opWord ω a (X.op ω a) ∈ T.heap := fun ω a => (hop ω a).exists.choose_spec
    refine ⟨X, ?_⟩
    cases T with
    | mk A H =>
      simp only [Rep, TokenClass.mk.injEq, heq_eq_eq]
      refine ⟨rfl, ?_⟩
      ext w
      constructor
      · rintro (⟨R, a, ha, rfl⟩ | ⟨ω, a, rfl⟩)
        · exact ha
        · exact hopX ω a
      · intro hw
        rcases hshape w hw with ⟨R, hR⟩ | ⟨ω, hω⟩
        · have h : wordMap (fun _ => PUnit.unit) w =
              Sum.inr (Sum.inl R) :: (List.ofFn fun _ : Fin (Sg.relArity R) => PUnit.unit).map
                Sum.inl := by
            rw [List.ofFn_const, List.map_replicate]; exact hR.symm
          obtain ⟨a, rfl, -⟩ := exists_of_wordMap_eq_cons _ w _ _ h
          exact Or.inl ⟨R, a, hw, rfl⟩
        · have h : wordMap (fun _ => PUnit.unit) w =
              Sum.inr (Sum.inr ω) ::
                (List.ofFn fun _ : Fin (Sg.opArity ω + 1) => PUnit.unit).map Sum.inl := by
            rw [List.ofFn_const, List.map_replicate]; exact hω.symm
          obtain ⟨c, rfl, -⟩ := exists_of_wordMap_eq_cons _ w _ _ h
          have hc : (Sum.inr (Sum.inr ω) :: (List.ofFn c).map Sum.inl : Word A Sg.core) =
              Str.opWord ω (Fin.init c) (c (Fin.last _)) := by
            rw [Str.opWord, ← map_inl_ofFn_snoc, Fin.snoc_init_self]
          rw [hc] at hw ⊢
          have := (hop ω (Fin.init c)).unique hw (hopX ω (Fin.init c))
          rw [this]
          exact X.opRecord_mem_heap ω (Fin.init c)

theorem Rep_injective_obj {Sg : AlgSig.{v}} : Function.Injective (Rep.{u} Sg).obj := by
  rintro ⟨A, r, o⟩ ⟨A', r', o'⟩ h
  simp only [Rep, TokenClass.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  rw [heq_eq_eq] at h
  have hr : r = r' := by
    funext R; ext a
    rw [← Str.relRecord_mem_heap_iff ⟨A, r, o⟩, ← Str.relRecord_mem_heap_iff ⟨A, r', o'⟩]
    exact iff_of_eq (congrArg (_ ∈ ·) h)
  have ho : o = o' := by
    funext ω a
    have := Str.opRecord_mem_heap ⟨A, r, o⟩ ω a
    change _ ∈ Str.heap ⟨A, r, o⟩ at this
    rw [h] at this
    exact ((Str.opWord_mem_heap_iff ⟨A, r', o'⟩ ω a _).mp this)
  subst hr ho
  rfl

/-! ### Location of finite limits (§3.2) -/

namespace Str

variable {Sg : AlgSig.{v}}

/-- The componentwise product of structures. -/
def prod (X Y : Str.{u} Sg) : Str.{u} Sg where
  carrier := X.carrier × Y.carrier
  rel R := {a | Prod.fst ∘ a ∈ X.rel R ∧ Prod.snd ∘ a ∈ Y.rel R}
  op ω a := (X.op ω (Prod.fst ∘ a), Y.op ω (Prod.snd ∘ a))

/-- The product cone. -/
def prodFan (X Y : Str.{u} Sg) : Limits.BinaryFan X Y :=
  Limits.BinaryFan.mk (P := X.prod Y)
    ⟨Prod.fst, fun _ _ h => h.1, fun _ _ => rfl⟩ ⟨Prod.snd, fun _ _ h => h.2, fun _ _ => rfl⟩

/-- `Str.prod` is a categorical product. -/
def prodIsLimit (X Y : Str.{u} Sg) : Limits.IsLimit (X.prodFan Y) :=
  Limits.BinaryFan.isLimitMk
    (fun c => ⟨fun x => (c.fst.toFun x, c.snd.toFun x),
      fun R a ha => ⟨c.fst.preserves_rel R a ha, c.snd.preserves_rel R a ha⟩,
      fun ω a => Prod.ext (c.fst.map_op ω a) (c.snd.map_op ω a)⟩)
    (fun _ => rfl) (fun _ => rfl)
    (fun c m h₁ h₂ => by
      apply Hom.ext; funext x
      exact Prod.ext (congrArg (fun k : Hom _ _ => k.toFun x) h₁)
        (congrArg (fun k : Hom _ _ => k.toFun x) h₂))

/-- The key fact behind product preservation: a word whose two projections are records is a
record of the product. -/
lemma mem_prod_heap {X Y : Str.{u} Sg} (w : Word (X.carrier × Y.carrier) Sg.core)
    (h₁ : wordMap Prod.fst w ∈ X.heap) (h₂ : wordMap Prod.snd w ∈ Y.heap) :
    w ∈ (X.prod Y).heap := by
  rcases h₁ with ⟨R, a, ha, h⟩ | ⟨ω, a, h⟩
  · obtain ⟨c, rfl, hc⟩ := exists_of_wordMap_eq_cons _ w _ _ h
    rw [wordMap_inr_cons_map_inl] at h₂
    refine Or.inl ⟨R, c, ⟨hc ▸ ha, ?_⟩, rfl⟩
    exact (Y.relRecord_mem_heap_iff R _).mp h₂
  · rw [opRecord_eq, opWord, ← map_inl_ofFn_snoc] at h
    obtain ⟨c, rfl, hc⟩ := exists_of_wordMap_eq_cons _ w _ _ h
    have hc1 : Prod.fst ∘ Fin.init c = a := by
      have := congrArg Fin.init hc
      rw [Fin.init_snoc] at this
      exact this
    have hc2 : (c (Fin.last _)).1 = X.op ω a := by
      have := congrFun hc (Fin.last _)
      rw [Fin.snoc_last] at this
      exact this
    rw [wordMap_inr_cons_map_inl, ← Fin.snoc_init_self c, Fin.comp_snoc, map_inl_ofFn_snoc] at h₂
    have h₂' := (Y.opWord_mem_heap_iff ω _ _).mp h₂
    have hlast : c (Fin.last _) = (X.prod Y).op ω (Fin.init c) := by
      refine Prod.ext ?_ ?_
      · show (c (Fin.last _)).1 = X.op ω (Prod.fst ∘ Fin.init c)
        rw [hc2, hc1]
      · exact h₂'
    refine Or.inr ⟨ω, Fin.init c, ?_⟩
    conv_lhs => rw [← Fin.snoc_init_self c, hlast]
    exact congrArg (List.cons _) (map_inl_ofFn_snoc _ _)

/-- The equalizer of `f, g` as a substructure. -/
def equalizer {X Y : Str.{u} Sg} (f g : X ⟶ Y) : Str.{u} Sg where
  carrier := {x : X.carrier // f.toFun x = g.toFun x}
  rel R := {a | Subtype.val ∘ a ∈ X.rel R}
  op ω a := ⟨X.op ω (Subtype.val ∘ a), by
    rw [f.map_op, g.map_op]
    congr 1
    funext j
    exact (a j).2⟩

/-- The equalizer fork. -/
def equalizerFork {X Y : Str.{u} Sg} (f g : X ⟶ Y) : Limits.Fork f g :=
  Limits.Fork.ofι (P := equalizer f g) ⟨Subtype.val, fun _ _ h => h, fun _ _ => rfl⟩
    (Hom.ext (funext fun x => x.2))

/-- `Str.equalizer` is a categorical equalizer. -/
def equalizerIsLimit {X Y : Str.{u} Sg} (f g : X ⟶ Y) : Limits.IsLimit (equalizerFork f g) :=
  Limits.Fork.IsLimit.mk _
    (fun c => ⟨fun x => ⟨c.ι.toFun x, congrArg (fun k : Hom _ _ => k.toFun x) c.condition⟩,
      fun R a ha => c.ι.preserves_rel R a ha,
      fun ω a => Subtype.ext (c.ι.map_op ω a)⟩)
    (fun _ => rfl)
    (fun c m h => by
      apply Hom.ext; funext x
      exact Subtype.ext (congrArg (fun k : Hom _ _ => k.toFun x) h))

lemma mem_equalizer_heap {X Y : Str.{u} Sg} (f g : X ⟶ Y)
    (w : Word (equalizer f g).carrier Sg.core) (h : wordMap Subtype.val w ∈ X.heap) :
    w ∈ (equalizer f g).heap := by
  rcases h with ⟨R, a, ha, h⟩ | ⟨ω, a, h⟩
  · obtain ⟨c, rfl, hc⟩ := exists_of_wordMap_eq_cons _ w _ _ h
    exact Or.inl ⟨R, c, show Subtype.val ∘ c ∈ X.rel R from hc ▸ ha, rfl⟩
  · rw [opRecord_eq, opWord, ← map_inl_ofFn_snoc] at h
    obtain ⟨c, rfl, hc⟩ := exists_of_wordMap_eq_cons _ w _ _ h
    have hc1 : Subtype.val ∘ Fin.init c = a := by
      have := congrArg Fin.init hc
      rw [Fin.init_snoc] at this
      exact this
    have hc2 : (c (Fin.last _)).1 = X.op ω a := by
      have := congrFun hc (Fin.last _)
      rw [Fin.snoc_last] at this
      exact this
    have hlast : c (Fin.last _) = (equalizer f g).op ω (Fin.init c) := by
      apply Subtype.ext
      show (c (Fin.last _)).1 = X.op ω (Subtype.val ∘ Fin.init c)
      rw [hc2, hc1]
    refine Or.inr ⟨ω, Fin.init c, ?_⟩
    conv_lhs => rw [← Fin.snoc_init_self c, hlast]
    exact congrArg (List.cons _) (map_inl_ofFn_snoc _ _)

end Str

/-- `Rep` sends the product cone to a limit cone. -/
def Rep_prodIsLimit {Sg : AlgSig.{v}} (X Y : Str.{u} Sg) :
    Limits.IsLimit ((Rep Sg).mapCone (X.prodFan Y)) :=
  (Limits.isLimitMapConeBinaryFanEquiv _ _ _).symm <| Limits.BinaryFan.isLimitMk
    (fun c => TokenClass.Hom.mk (fun x => (c.fst.toFun x, c.snd.toFun x)) fun w hw => by
      refine Str.mem_prod_heap _ ?_ ?_
      · have := c.fst.preserves w hw
        show (wordMap Prod.fst ∘ wordMap (fun x => (c.fst.toFun x, c.snd.toFun x))) w ∈ X.heap
        rwa [← wordMap_comp]
      · have := c.snd.preserves w hw
        show (wordMap Prod.snd ∘ wordMap (fun x => (c.fst.toFun x, c.snd.toFun x))) w ∈ Y.heap
        rwa [← wordMap_comp])
    (fun _ => rfl) (fun _ => rfl)
    (fun c m h₁ h₂ => by
      apply TokenClass.Hom.ext; funext x
      exact Prod.ext (congrArg (fun k : TokenClass.Hom _ _ => k.toFun x) h₁)
        (congrArg (fun k : TokenClass.Hom _ _ => k.toFun x) h₂))

/-- **Proposition 3.3** (part): `Rep` preserves binary products. -/
instance Rep_preservesBinaryProducts (Sg : AlgSig.{v}) [Limits.HasBinaryProducts (Str.{u} Sg)] :
    Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair) (Rep.{u} Sg) where
  preservesLimit {K} :=
    haveI : Limits.PreservesLimit (Limits.pair (K.obj ⟨.left⟩) (K.obj ⟨.right⟩)) (Rep.{u} Sg) :=
      Limits.preservesLimit_of_preserves_limit_cone (Str.prodIsLimit _ _) (Rep_prodIsLimit _ _)
    Limits.preservesLimit_of_iso_diagram (Rep.{u} Sg) (Limits.diagramIsoPair K).symm

/-- `Rep` sends the equalizer fork to a limit cone. -/
def Rep_equalizerIsLimit {Sg : AlgSig.{v}} {X Y : Str.{u} Sg} (f g : X ⟶ Y) :
    Limits.IsLimit ((Rep Sg).mapCone (Str.equalizerFork f g)) :=
  (Limits.isLimitMapConeForkEquiv _ _).symm <| Limits.Fork.IsLimit.mk _
    (fun c => TokenClass.Hom.mk
      (fun x => ⟨c.ι.toFun x, congrArg (fun k : TokenClass.Hom _ _ => k.toFun x) c.condition⟩)
      fun w hw => by
        refine Str.mem_equalizer_heap f g _ ?_
        have := c.ι.preserves w hw
        show (wordMap Subtype.val ∘ wordMap _) w ∈ X.heap
        rwa [← wordMap_comp])
    (fun _ => rfl)
    (fun c m h => by
      apply TokenClass.Hom.ext; funext x
      exact Subtype.ext (congrArg (fun k : TokenClass.Hom _ _ => k.toFun x) h))

/-- **Proposition 3.3** (part): `Rep` preserves equalizers. -/
instance Rep_preservesEqualizers (Sg : AlgSig.{v}) [Limits.HasEqualizers (Str.{u} Sg)] :
    Limits.PreservesLimitsOfShape Limits.WalkingParallelPair (Rep.{u} Sg) where
  preservesLimit {K} :=
    haveI : Limits.PreservesLimit (Limits.parallelPair (K.map Limits.WalkingParallelPairHom.left)
        (K.map Limits.WalkingParallelPairHom.right)) (Rep.{u} Sg) :=
      Limits.preservesLimit_of_preserves_limit_cone (Str.equalizerIsLimit _ _)
        (Rep_equalizerIsLimit _ _)
    Limits.preservesLimit_of_iso_diagram (Rep.{u} Sg) (Limits.diagramIsoParallelPair K).symm

/-- **Proposition 3.3** (part): `Rep` need not preserve the terminal object. Witness: the pure
signature with one binary operation; the one-element algebra's heap omits the empty word
present in the ambient terminal heap. -/
theorem Rep_not_preservesTerminal :
    ∃ (Sg : AlgSig.{0}) (X : Str.{0} Sg), Nonempty (Limits.IsTerminal X) ∧
      ¬ Nonempty (Limits.IsTerminal ((Rep Sg).obj X)) := by
  refine ⟨⟨PEmpty, PEmpty.elim, Unit, fun _ => 2⟩, ⟨PUnit, fun R => R.elim, fun _ _ => ⟨⟩⟩,
    ⟨Limits.IsTerminal.ofUniqueHom (fun _ => ⟨fun _ => ⟨⟩, fun R => R.elim, fun _ _ => rfl⟩)
      (fun _ _ => Str.Hom.ext (funext fun _ => rfl))⟩, ?_⟩
  rintro ⟨h⟩
  have f := h.from (TokenClass.terminal _)
  have := f.preserves [] trivial
  exact Str.nil_notMem_heap _ this

/-- **Example 3.4**: for binary addition on `ZMod 2`, the relational exponential relation
`R_+(f,g,h) ↔ ∀ x y, f x + g y = h (x + y)` is not total at `(f,g) = (0, id)`. -/
theorem relationalExponential_not_total :
    ¬ ∃ h : ZMod 2 → ZMod 2, ∀ x y : ZMod 2, (0 : ZMod 2) + y = h (x + y) := by
  rintro ⟨h, hh⟩
  have h1 : h 0 = 0 := by simpa using (hh 0 0).symm
  have h2 : h 0 = 1 := by
    have := hh 1 1
    rw [show (1 : ZMod 2) + 1 = 0 by decide, zero_add] at this
    exact this.symm
  rw [h1] at h2
  exact absurd h2 (by decide)

/-! ### Direct images and algebraic quotients (§3.3) -/

/-- The direct image `q_! H = F_E(q)(H)`. -/
def directImage {A B : Type u} {E : Type v} (q : A → B) (H : Set (Word A E)) : Set (Word B E) :=
  wordMap q '' H

/-- `ker q` is a congruence of `X`: operations respect the kernel. -/
def IsCongruenceKer {Sg : AlgSig.{v}} (X : Str.{u} Sg) {B : Type u} (q : X.carrier → B) : Prop :=
  ∀ (ω : Sg.opSymbols) (a a' : Fin (Sg.opArity ω) → X.carrier),
    (∀ j, q (a j) = q (a' j)) → q (X.op ω a) = q (X.op ω a')

/-- **Theorem 3.5** (the quotient criterion). For a total algebra `X` in a pure operation
signature and a surjection `q`, the direct image of `H_X` is a total algebra's tokenization
exactly when `ker q` is a congruence. -/
theorem quotient_criterion {Sg : AlgSig.{v}} (hpure : IsEmpty Sg.relSymbols)
    (X : Str.{u} Sg) {B : Type u} (q : X.carrier → B) (hq : Function.Surjective q) :
    (TokenClass.mk B (directImage q X.heap)).IsAlgebraic ↔ IsCongruenceKer X q := by
  -- every member of the direct image is the image of an operation record
  have hmem : ∀ w, w ∈ directImage q X.heap ↔
      ∃ ω a, w = Str.opWord ω (q ∘ a) (q (X.op ω a)) := by
    intro w
    constructor
    · rintro ⟨w', (⟨R, _, _, _⟩ | ⟨ω, a, rfl⟩), rfl⟩
      · exact hpure.elim R
      · exact ⟨ω, a, Str.wordMap_opRecord q ω a⟩
    · rintro ⟨ω, a, rfl⟩
      exact ⟨_, X.opRecord_mem_heap ω a, Str.wordMap_opRecord q ω a⟩
  constructor
  · rintro ⟨-, hop⟩ ω a a' haa'
    have hq' : q ∘ a = q ∘ a' := funext haa'
    have h1 : Str.opWord ω (q ∘ a) (q (X.op ω a)) ∈ directImage q X.heap :=
      (hmem _).mpr ⟨ω, a, rfl⟩
    have h2 : Str.opWord ω (q ∘ a) (q (X.op ω a')) ∈ directImage q X.heap :=
      (hmem _).mpr ⟨ω, a', by rw [hq']⟩
    exact (hop ω (q ∘ a)).unique h1 h2
  · intro hc
    refine ⟨?_, fun ω b => ?_⟩
    · rintro w ⟨w', hw', rfl⟩
      rw [shape_wordMap]
      exact ((Rep_image_iff ((Rep Sg).obj X)).mp ⟨X, rfl⟩).1 w' hw'
    · obtain ⟨a, rfl⟩ := hq.comp_left b
      refine ⟨q (X.op ω a), (hmem _).mpr ⟨ω, a, rfl⟩, fun c hc' => ?_⟩
      obtain ⟨ω', a', h⟩ := (hmem _).mp hc'
      have hω := Str.opWord_symbol_eq h
      subst hω
      obtain ⟨h1, rfl⟩ := Str.opWord_inj h
      exact hc ω a' a fun j => (congrFun h1 j).symm

/-- **Theorem 3.5** (continued): the quotient structure is unique and `q` becomes a
surjective homomorphism onto it. -/
theorem quotient_exists_unique {Sg : AlgSig.{v}} (hpure : IsEmpty Sg.relSymbols)
    (X : Str.{u} Sg) {B : Type u} (q : X.carrier → B) (hq : Function.Surjective q)
    (hc : IsCongruenceKer X q) :
    ∃! Y : Str.{u} Sg, (Rep Sg).obj Y = TokenClass.mk B (directImage q X.heap) := by
  obtain ⟨Y, hY⟩ := (Rep_image_iff _).mpr ((quotient_criterion hpure X q hq).mpr hc)
  exact ⟨Y, hY, fun Y' hY' => Rep_injective_obj (hY'.trans hY.symm)⟩

/-- **Example 3.6**: `A = {0,1,2}`, `u 0 = 0`, `u 1 = u 2 = 2`, `q 0 = q 1 = a`, `q 2 = b`:
the image is a Token class but not a unary algebra. -/
theorem bad_quotient_example :
    let Sg : AlgSig.{0} := ⟨PEmpty, PEmpty.elim, Unit, fun _ => 1⟩
    let X : Str.{0} Sg := ⟨Fin 3, fun R => R.elim, fun _ a => if a 0 = 0 then 0 else 2⟩
    let q : Fin 3 → Bool := fun i => i = 2
    ¬ (TokenClass.mk Bool (directImage q X.heap)).IsAlgebraic := by
  intro Sg X q h
  obtain ⟨-, hop⟩ := h
  have h1 : Str.opWord (Sg := Sg) () (fun _ => false) false ∈ directImage q X.heap :=
    ⟨X.opRecord () (fun _ => 0), X.opRecord_mem_heap _ _, by decide⟩
  have h2 : Str.opWord (Sg := Sg) () (fun _ => false) true ∈ directImage q X.heap :=
    ⟨X.opRecord () (fun _ => 1), X.opRecord_mem_heap _ _, by decide⟩
  exact Bool.false_ne_true ((hop () (fun _ => false)).unique h1 h2)

end AT

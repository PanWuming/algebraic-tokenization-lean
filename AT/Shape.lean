import AT.Basic

/-!
# Shapes and the exact relational presentation (paper §2.2)

* `AT.Shape E = ({□} ⊔ E)^*`, `AT.shape w`, `AT.blanks s = k(s)`.
* `AT.fill s : (Fin k(s) → A) → Word A E` is `ι_{s,A}`.
* Proposition 2.3 (`AT.shapeDecomposition`): `∐_s A^{k(s)} ≅ F_E(A)`, natural in `A`.
* Finitary relational signatures, structures, homomorphisms, the category `AT.RelStr Sg`.
* Theorem 2.4 (`AT.relationalEquivalence`): `TS_E ≅ Rel(Sg_E^all)` concretely.
-/

universe u v

namespace AT

open CategoryTheory

/-- `Sh_E = ({□} ⊔ E)^*`; the blank is `Sum.inl ()`. -/
abbrev Shape (E : Type v) := Word PUnit.{u+1} E

variable {A B : Type u} {E : Type v}

/-- The shape of a word: replace every carrier entry by a blank. -/
def shape (w : Word A E) : Shape.{u} E := wordMap (fun _ => PUnit.unit) w

/-- `k(s)`: the number of blanks in a shape. -/
abbrev blanks : Shape.{u} E → ℕ
  | [] => 0
  | Sum.inl _ :: s => blanks s + 1
  | Sum.inr _ :: s => blanks s

@[simp] lemma blanks_nil : blanks ([] : Shape.{u} E) = 0 := rfl
@[simp] lemma blanks_cons_inl (x : PUnit) (s : Shape.{u} E) :
    blanks (Sum.inl x :: s) = blanks s + 1 := rfl
@[simp] lemma blanks_cons_inr (e : E) (s : Shape.{u} E) : blanks (Sum.inr e :: s) = blanks s := rfl

lemma blanks_eq_length_filter (s : Shape.{u} E) : blanks s = (s.filter Sum.isLeft).length := by
  induction s with
  | nil => rfl
  | cons x s ih => rcases x with x | e <;> simp [ih, List.filter_cons]

/-- The ordered tuple of carrier entries of a word (retaining multiplicities). -/
def carrierEntries : Word A E → List A
  | [] => []
  | Sum.inl a :: w => a :: carrierEntries w
  | Sum.inr _ :: w => carrierEntries w

@[simp] lemma carrierEntries_nil : carrierEntries ([] : Word A E) = [] := rfl
@[simp] lemma carrierEntries_cons_inl (a : A) (w : Word A E) :
    carrierEntries (Sum.inl a :: w) = a :: carrierEntries w := rfl
@[simp] lemma carrierEntries_cons_inr (e : E) (w : Word A E) :
    carrierEntries (Sum.inr e :: w) = carrierEntries w := rfl

@[simp] lemma shape_nil : shape ([] : Word A E) = [] := rfl
@[simp] lemma shape_cons_inl (a : A) (w : Word A E) :
    shape (Sum.inl a :: w) = Sum.inl PUnit.unit :: shape w := rfl
@[simp] lemma shape_cons_inr (e : E) (w : Word A E) :
    shape (Sum.inr e :: w) = Sum.inr e :: shape w := rfl

lemma length_carrierEntries (w : Word A E) : (carrierEntries w).length = blanks (shape w) := by
  induction w with
  | nil => rfl
  | cons x w ih => rcases x with a | e <;> simp [ih]

/-- `ι_{s,A}`: fill the blanks of `s` from left to right with a tuple. -/
def fill : (s : Shape.{u} E) → (Fin (blanks s) → A) → Word A E
  | [], _ => []
  | Sum.inl _ :: s, a =>
      Sum.inl (a ⟨0, Nat.succ_pos _⟩) :: fill s (fun i => a ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
  | Sum.inr e :: s, a => Sum.inr e :: fill s a

@[simp] lemma fill_nil (a : Fin (blanks ([] : Shape.{u} E)) → A) : fill [] a = [] := by
  simp [fill]
@[simp] lemma fill_cons_inl (x : PUnit) (s : Shape.{u} E) (a : Fin (blanks s + 1) → A) :
    fill (Sum.inl x :: s) a = Sum.inl (a 0) :: fill s (fun i => a i.succ) := by
  simp only [fill]; rfl
@[simp] lemma fill_cons_inr (e : E) (s : Shape.{u} E) (a : Fin (blanks s) → A) :
    fill (Sum.inr e :: s) a = Sum.inr e :: fill s a := by
  simp only [fill]

@[simp] lemma shape_fill (s : Shape.{u} E) (a : Fin (blanks s) → A) : shape (fill s a) = s := by
  induction s with
  | nil => rfl
  | cons x s ih => rcases x with x | e <;> simp [ih]

/-- Naturality of filling: `F_E(f) ∘ ι_{s,A} = ι_{s,B} ∘ f^{k(s)}`. -/
lemma wordMap_fill (f : A → B) (s : Shape.{u} E) (a : Fin (blanks s) → A) :
    wordMap f (fill s a) = fill s (f ∘ a) := by
  induction s with
  | nil => rfl
  | cons x s ih => rcases x with x | e <;> simp [ih, Function.comp_def]

@[simp] lemma shape_wordMap (f : A → B) (w : Word A E) : shape (wordMap f w) = shape w := by
  simp only [shape, ← Function.comp_apply (f := wordMap _), ← wordMap_comp]

lemma carrierEntries_fill (s : Shape.{u} E) (a : Fin (blanks s) → A) :
    carrierEntries (fill s a) = List.ofFn a := by
  induction s with
  | nil => simp
  | cons x s ih => rcases x with x | e <;> simp [ih, List.ofFn_succ]

/-- The tuple of carrier entries of `w`, indexed by the blanks of its shape. -/
def entries (w : Word A E) (i : Fin (blanks (shape w))) : A :=
  (carrierEntries w)[i.val]'(by rw [length_carrierEntries]; exact i.2)

lemma fill_eq_of_entries : ∀ (w : Word A E) (s : Shape.{u} E) (hs : shape w = s)
    (g : Fin (blanks s) → A),
    (∀ i : Fin (blanks s),
      g i = (carrierEntries w)[i.1]'(by rw [length_carrierEntries, hs]; exact i.2)) →
    fill s g = w
  | [], [], _, _, _ => rfl
  | [], Sum.inl _ :: _, hs, _, _ => by simp at hs
  | [], Sum.inr _ :: _, hs, _, _ => by simp at hs
  | Sum.inl a :: w, [], hs, _, _ => by simp at hs
  | Sum.inl a :: w, Sum.inr _ :: _, hs, _, _ => by simp at hs
  | Sum.inl a :: w, Sum.inl x :: s, hs, g, hg => by
      have hs' : shape w = s := by simpa using hs
      rw [fill_cons_inl]
      congr 1
      · exact congrArg Sum.inl (hg 0)
      · exact fill_eq_of_entries w s hs' _ (fun i => hg i.succ)
  | Sum.inr e :: w, [], hs, _, _ => by simp at hs
  | Sum.inr e :: w, Sum.inl _ :: _, hs, _, _ => by simp at hs
  | Sum.inr e :: w, Sum.inr e' :: s, hs, g, hg => by
      obtain ⟨rfl, hs'⟩ : e = e' ∧ shape w = s := by simpa using hs
      rw [fill_cons_inr]
      congr 1
      exact fill_eq_of_entries w s hs' _ hg

lemma fill_shape_entries (w : Word A E) : fill (shape w) (entries w) = w :=
  fill_eq_of_entries w _ rfl _ (fun _ => rfl)

lemma entries_fill (s : Shape.{u} E) (a : Fin (blanks s) → A) :
    HEq (entries (fill s a)) a := by
  have h := shape_fill s a
  have key : ∀ (s' : Shape.{u} E) (hs : s' = s) (g : Fin (blanks s') → A),
      (∀ i, g i = a (Fin.cast (by rw [hs]) i)) → HEq g a := by
    intro s' hs g hg; subst hs; exact heq_of_eq (funext hg)
  refine key _ h _ fun i => ?_
  simp only [entries, carrierEntries_fill, List.getElem_ofFn]
  rfl

/-- **Proposition 2.3** (natural decomposition by sequence shape):
`θ_A : ∐_{s} A^{k(s)} ≅ F_E(A)`. -/
def shapeDecomposition (A : Type u) (E : Type v) :
    (Σ s : Shape.{u} E, Fin (blanks s) → A) ≃ Word A E where
  toFun p := fill p.1 p.2
  invFun w := ⟨shape w, entries w⟩
  left_inv _ := Sigma.ext (shape_fill _ _) (entries_fill _ _)
  right_inv w := fill_shape_entries w

/-- Naturality of `θ` (Proposition 2.3): `F_E(f) ∘ θ_A = θ_B ∘ ∐_s f^{k(s)}`. -/
lemma shapeDecomposition_naturality (f : A → B) (p : Σ s : Shape.{u} E, Fin (blanks s) → A) :
    wordMap f (shapeDecomposition A E p) = shapeDecomposition B E ⟨p.1, f ∘ p.2⟩ :=
  wordMap_fill f p.1 p.2

/-- Concatenation of shapes adds blank counts: `k(st) = k(s) + k(t)` (eq. 2.3). -/
lemma blanks_append (s t : Shape.{u} E) : blanks (s ++ t) = blanks s + blanks t := by
  induction s with
  | nil => simp
  | cons x s ih => rcases x with x | e <;> simp [ih, Nat.add_right_comm]

/-! ### Finitary relational signatures and structures -/

/-- A finitary relational signature: a set of symbols with arities in `ℕ` (arity 0 allowed). -/
structure RelSig where
  symbols : Type v
  arity : symbols → ℕ

/-- A relational structure: a carrier with one `arity R`-ary relation per symbol.
A zero-ary relation is a truth value (a subset of `X^0 = {()}`). -/
structure RelStr (Sg : RelSig.{v}) where
  carrier : Type u
  rel : ∀ R : Sg.symbols, Set (Fin (Sg.arity R) → carrier)

namespace RelStr

variable {Sg : RelSig.{v}}

/-- Homomorphisms preserve relations in the forward direction. -/
@[ext]
structure Hom (X Y : RelStr.{u} Sg) where
  toFun : X.carrier → Y.carrier
  preserves : ∀ (R : Sg.symbols) (a : Fin (Sg.arity R) → X.carrier), a ∈ X.rel R → toFun ∘ a ∈ Y.rel R

/-- The category `Rel(Sg)`. -/
instance : Category (RelStr.{u} Sg) where
  Hom := Hom
  id X := ⟨id, fun R a h => h⟩
  comp f g := ⟨g.toFun ∘ f.toFun, fun R a h => g.preserves R _ (f.preserves R a h)⟩

@[simp] lemma comp_toFun {X Y Z : RelStr.{u} Sg} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toFun = g.toFun ∘ f.toFun := rfl

/-- The underlying-set functor `U_Sg`. -/
def forget : RelStr.{u} Sg ⥤ Type u where
  obj X := X.carrier
  map f := TypeCat.ofHom f.toFun

instance : (forget (Sg := Sg)).Faithful where
  map_injective {X Y} f g h := Hom.ext (by
    have := congrArg (fun k : X.carrier ⟶ Y.carrier => (TypeCat.homEquiv k : _ → _)) h
    simpa [forget] using this)

end RelStr

/-- The all-shape signature `Sg_E^all`: one symbol `R_s` of arity `k(s)` per shape. -/
abbrev allShapeSig (E : Type v) : RelSig where
  symbols := Shape.{u} E
  arity := blanks

/-- `R_s^H = {a : ι_{s,A}(a) ∈ H}` (eq. 2.2). -/
def TokenClass.toRelStr (T : TokenClass.{u} E) : RelStr.{u} (allShapeSig.{u} E) where
  carrier := T.carrier
  rel s := {a | fill s a ∈ T.heap}

/-- `H = ⋃_s ι_{s,A}(R_s)`. -/
def RelStr.toTokenClass (X : RelStr.{u} (allShapeSig.{u} E)) : TokenClass.{u} E where
  carrier := X.carrier
  heap := {w | ∃ s a, a ∈ X.rel s ∧ fill s a = w}

/-- The functor `TS_E → Rel(Sg_E^all)`. -/
def toRel : TokenClass.{u} E ⥤ RelStr.{u} (allShapeSig.{u} E) where
  obj := TokenClass.toRelStr
  map {X Y} f := ⟨f.toFun, fun s a h => by
    show fill s (f.toFun ∘ a) ∈ Y.heap
    exact (wordMap_fill f.toFun s a) ▸ f.preserves _ h⟩

/-- The functor `Rel(Sg_E^all) → TS_E`. -/
def ofRel : RelStr.{u} (allShapeSig.{u} E) ⥤ TokenClass.{u} E where
  obj := RelStr.toTokenClass
  map f := ⟨f.toFun, by
    rintro w ⟨s, a, ha, rfl⟩
    exact ⟨s, f.toFun ∘ a, f.preserves s a ha, (wordMap_fill _ _ _).symm⟩⟩

/-- **Theorem 2.4** (exact relational presentation): a concrete isomorphism
`TS_E ≅ Rel(Sg_E^all)` retaining carriers and underlying functions. We state it as an
equivalence whose two functors are mutually inverse on the nose at the level of objects
and commute with the carrier functors. -/
theorem relationalEquivalence_obj (T : TokenClass.{u} E) : ofRel.obj (toRel.obj T) = T := by
  cases T with
  | mk A H =>
    simp only [ofRel, toRel, RelStr.toTokenClass, TokenClass.toRelStr, TokenClass.mk.injEq,
      heq_eq_eq, true_and]
    ext w
    constructor
    · rintro ⟨s, a, ha, rfl⟩; exact ha
    · intro hw; exact ⟨shape w, entries w, by simpa [fill_shape_entries] using hw,
        fill_shape_entries w⟩

theorem relationalEquivalence_obj' (X : RelStr.{u} (allShapeSig.{u} E)) :
    toRel.obj (ofRel.obj X) = X := by
  cases X with
  | mk A R =>
    simp only [ofRel, toRel, RelStr.toTokenClass, TokenClass.toRelStr, RelStr.mk.injEq,
      heq_eq_eq, true_and]
    funext s; ext a
    constructor
    · rintro ⟨t, b, hb, h⟩
      have h1 := congrArg shape h
      rw [shape_fill, shape_fill] at h1
      subst h1
      have h2 := congrArg carrierEntries h
      rw [carrierEntries_fill, carrierEntries_fill] at h2
      rwa [List.ofFn_inj.mp h2] at hb
    · intro h; exact ⟨s, a, h, rfl⟩

lemma TokenClass.eqToHom_toFun {X Y : TokenClass.{u} E} (h : X = Y) :
    (eqToHom h).toFun = cast (congrArg TokenClass.carrier h) := by subst h; rfl

lemma RelStr.eqToHom_toFun {Sg : RelSig.{v}} {X Y : RelStr.{u} Sg} (h : X = Y) :
    (eqToHom h).toFun = cast (congrArg RelStr.carrier h) := by subst h; rfl

/-- `toRel ⋙ ofRel = 𝟭` on the nose. -/
theorem toRel_comp_ofRel : toRel ⋙ ofRel = 𝟭 (TokenClass.{u} E) :=
  CategoryTheory.Functor.ext relationalEquivalence_obj (fun X Y f => by
    apply TokenClass.Hom.ext; funext x
    simp only [Functor.comp_map, Functor.id_map, TokenClass.comp_toFun, TokenClass.eqToHom_toFun,
      Function.comp_apply]
    exact ((cast_eq _ _).trans (congrArg f.toFun (cast_eq _ x))).symm)

/-- `ofRel ⋙ toRel = 𝟭` on the nose. -/
theorem ofRel_comp_toRel : ofRel ⋙ toRel = 𝟭 (RelStr.{u} (allShapeSig.{u} E)) :=
  CategoryTheory.Functor.ext relationalEquivalence_obj' (fun X Y f => by
    apply RelStr.Hom.ext; funext x
    simp only [Functor.comp_map, Functor.id_map, RelStr.comp_toFun, RelStr.eqToHom_toFun,
      Function.comp_apply]
    exact ((cast_eq _ _).trans (congrArg f.toFun (cast_eq _ x))).symm)

/-- The equivalence of categories `TS_E ≌ Rel(Sg_E^all)`. -/
def relationalEquivalence : TokenClass.{u} E ≌ RelStr.{u} (allShapeSig.{u} E) :=
  CategoryTheory.Equivalence.mk toRel ofRel (eqToIso toRel_comp_ofRel.symm) (eqToIso ofRel_comp_toRel)

theorem relationalEquivalence_forget :
    (relationalEquivalence (E := E)).functor ⋙ RelStr.forget = TokenClass.forget :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => rfl)

/-- Products in `TS_E` (eq. 2.4): carrier `A × B`, heap
`F_E(π_A)⁻¹(H_A) ∩ F_E(π_B)⁻¹(H_B)`. -/
def TokenClass.prod (T₁ T₂ : TokenClass.{u} E) : TokenClass.{u} E where
  carrier := T₁.carrier × T₂.carrier
  heap := {w | wordMap Prod.fst w ∈ T₁.heap ∧ wordMap Prod.snd w ∈ T₂.heap}

/-- The terminal object `({*}, E, F_E({*}))`. -/
def TokenClass.terminal (E : Type v) : TokenClass.{u} E where
  carrier := PUnit
  heap := Set.univ

/-- The equalizer of `f, g`: restrict to `S = {a : f a = g a}` with the inverse-image heap. -/
def TokenClass.equalizer {T₁ T₂ : TokenClass.{u} E} (f g : T₁ ⟶ T₂) : TokenClass.{u} E where
  carrier := {a : T₁.carrier // f.toFun a = g.toFun a}
  heap := {w | wordMap Subtype.val w ∈ T₁.heap}

/-- The product cone for `TokenClass.prod`. -/
def TokenClass.prodFan (T₁ T₂ : TokenClass.{u} E) : Limits.BinaryFan T₁ T₂ :=
  Limits.BinaryFan.mk (P := T₁.prod T₂)
    ⟨Prod.fst, fun _ h => h.1⟩ ⟨Prod.snd, fun _ h => h.2⟩

/-- `TokenClass.prod` is a categorical product. -/
def TokenClass.prodIsLimit (T₁ T₂ : TokenClass.{u} E) : Limits.IsLimit (T₁.prodFan T₂) :=
  Limits.BinaryFan.isLimitMk
    (fun c => ⟨fun x => (c.fst.toFun x, c.snd.toFun x), fun w hw => by
      refine ⟨?_, ?_⟩
      · have := c.fst.preserves w hw
        show (wordMap Prod.fst ∘ wordMap (fun x => (c.fst.toFun x, c.snd.toFun x))) w ∈ T₁.heap
        rwa [← wordMap_comp]
      · have := c.snd.preserves w hw
        show (wordMap Prod.snd ∘ wordMap (fun x => (c.fst.toFun x, c.snd.toFun x))) w ∈ T₂.heap
        rwa [← wordMap_comp]⟩)
    (fun _ => rfl) (fun _ => rfl)
    (fun c m h₁ h₂ => by
      apply TokenClass.Hom.ext; funext x
      exact Prod.ext (congrArg (fun k : Hom _ _ => k.toFun x) h₁)
        (congrArg (fun k : Hom _ _ => k.toFun x) h₂))

/-- `TS_E` has binary products (the ambient construction of eq. 2.4). -/
instance (T₁ T₂ : TokenClass.{u} E) : Limits.HasLimit (Limits.pair T₁ T₂) :=
  ⟨⟨⟨_, T₁.prodIsLimit T₂⟩⟩⟩

instance : Limits.HasBinaryProducts (TokenClass.{u} E) :=
  Limits.hasBinaryProducts_of_hasLimit_pair _

/-- `TokenClass.terminal` is terminal. -/
def TokenClass.terminalIsTerminal : Limits.IsTerminal (TokenClass.terminal.{u} E) :=
  Limits.IsTerminal.ofUniqueHom (fun _ => ⟨fun _ => PUnit.unit, fun _ _ => trivial⟩)
    (fun _ _ => TokenClass.Hom.ext (funext fun _ => rfl))

instance : Limits.HasTerminal (TokenClass.{u} E) :=
  Limits.IsTerminal.hasTerminal TokenClass.terminalIsTerminal

/-- The equalizer fork. -/
def TokenClass.equalizerFork {T₁ T₂ : TokenClass.{u} E} (f g : T₁ ⟶ T₂) : Limits.Fork f g :=
  Limits.Fork.ofι (P := TokenClass.equalizer f g) ⟨Subtype.val, fun _ h => h⟩
    (TokenClass.Hom.ext (funext fun x => x.2))

/-- `TokenClass.equalizer` is a categorical equalizer. -/
def TokenClass.equalizerIsLimit {T₁ T₂ : TokenClass.{u} E} (f g : T₁ ⟶ T₂) :
    Limits.IsLimit (TokenClass.equalizerFork f g) :=
  Limits.Fork.IsLimit.mk _
    (fun c => ⟨fun x => ⟨c.ι.toFun x, congrArg (fun k : Hom _ _ => k.toFun x) c.condition⟩,
      fun w hw => by
        have := c.ι.preserves w hw
        show (wordMap Subtype.val ∘ wordMap _) w ∈ T₁.heap
        rwa [← wordMap_comp]⟩)
    (fun _ => rfl)
    (fun c m h => by
      apply TokenClass.Hom.ext; funext x
      exact Subtype.ext (congrArg (fun k : Hom _ _ => k.toFun x) h))

instance {T₁ T₂ : TokenClass.{u} E} (f g : T₁ ⟶ T₂) :
    Limits.HasLimit (Limits.parallelPair f g) :=
  ⟨⟨⟨_, TokenClass.equalizerIsLimit f g⟩⟩⟩

instance : Limits.HasEqualizers (TokenClass.{u} E) :=
  Limits.hasEqualizers_of_hasLimit_parallelPair _

instance : Limits.HasFiniteProducts (TokenClass.{u} E) :=
  hasFiniteProducts_of_has_binary_and_terminal

instance : Limits.HasFiniteLimits (TokenClass.{u} E) :=
  Limits.hasFiniteLimits_of_hasEqualizers_and_finite_products

end AT

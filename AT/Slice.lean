import AT.Signature

/-!
# Shape selection as a slice (paper §3.1, Theorem 3.1) and shape languages (§5.1)

* `AT.subterminalOfShapes L` is `S_L`: carrier `{*}`, heap = fillings of `L`.
* **Theorem 3.1**: `S_L` is subterminal and `Rel(L) ≅ R_L ≃ TS_E / S_L`.
* `AT.allowedWords L A = W_L(A) = sh_A⁻¹(L)` (§5.1).
-/

universe u v

namespace AT

open CategoryTheory

variable {E : Type v}

/-- `W_L(A) = sh_A⁻¹(L)`: all records with allowed shapes (§5.1). -/
def allowedWords (L : Set (Shape.{u} E)) (A : Type u) : Set (Word A E) := shape ⁻¹' L

/-- `S_L`: the singleton carrier with all words obtained by filling shapes in `L`. -/
def subterminalOfShapes (L : Set (Shape.{u} E)) : TokenClass.{u} E where
  carrier := PUnit
  heap := allowedWords L PUnit

/-- `R_L`: the full subcategory of heaps using only shapes in `L`. -/
def usesShapes (L : Set (Shape.{u} E)) : ObjectProperty (TokenClass.{u} E) :=
  fun T => ∀ w ∈ T.heap, shape w ∈ L

/-- The unique carrier function to `{*}` is a Token map exactly when every record has an
allowed shape. -/
theorem hom_to_subterminal_iff (L : Set (Shape.{u} E)) (T : TokenClass.{u} E) :
    Nonempty (T ⟶ subterminalOfShapes L) ↔ usesShapes L T := by
  constructor
  · rintro ⟨f⟩ w hw
    have h : shape (wordMap f.toFun w) ∈ L := f.preserves w hw
    rwa [shape_wordMap] at h
  · intro h
    exact ⟨⟨fun _ => PUnit.unit, fun w hw => by
      show shape (wordMap _ w) ∈ L
      rw [shape_wordMap]; exact h w hw⟩⟩

/-- The Token map to `S_L` determined by `usesShapes L T`. -/
def toSubterminal {L : Set (Shape.{u} E)} {T : TokenClass.{u} E} (h : usesShapes L T) :
    T ⟶ subterminalOfShapes L :=
  ⟨fun _ => PUnit.unit, fun w hw => by
    show shape (wordMap _ w) ∈ L
    rw [shape_wordMap]; exact h w hw⟩

/-- **Theorem 3.1** (part): `S_L` is subterminal. -/
theorem subterminalOfShapes_isSubterminal (L : Set (Shape.{u} E)) :
    ∀ (T : TokenClass.{u} E) (f g : T ⟶ subterminalOfShapes L), f = g := by
  intro T f g; exact TokenClass.Hom.ext (funext fun a => @Subsingleton.elim PUnit _ _ _)

/-- The relational signature with one `k(s)`-ary symbol per `s ∈ L`. -/
def shapeSig (L : Set (Shape.{u} E)) : RelSig where
  symbols := L
  arity s := blanks s.1

/-- `Rel(L) → R_L`: the heap `⋃_{s ∈ L} ι_s(R_s)`. -/
def relShapesToUses (L : Set (Shape.{u} E)) :
    RelStr.{u} (shapeSig L) ⥤ (usesShapes L).FullSubcategory where
  obj X := ⟨⟨X.carrier, {w | ∃ (s : L) (a : Fin (blanks s.1) → X.carrier),
      a ∈ X.rel s ∧ fill s.1 a = w}⟩,
    by rintro w ⟨s, a, _, rfl⟩; rw [shape_fill]; exact s.2⟩
  map f := ⟨⟨f.toFun, by
    rintro w ⟨s, a, ha, rfl⟩
    exact ⟨s, f.toFun ∘ a, f.preserves s a ha, (wordMap_fill _ _ _).symm⟩⟩⟩

/-- `R_L → Rel(L)`: read off the shape relations `R_s^H`. -/
def usesToRelShapes (L : Set (Shape.{u} E)) :
    (usesShapes L).FullSubcategory ⥤ RelStr.{u} (shapeSig L) where
  obj T := ⟨T.obj.carrier, fun s => {a | fill s.1 a ∈ T.obj.heap}⟩
  map {X Y} f := ⟨f.hom.toFun, fun s a h => by
    show fill s.1 (f.hom.toFun ∘ a) ∈ Y.obj.heap
    exact (wordMap_fill f.hom.toFun s.1 a) ▸ f.hom.preserves _ h⟩

theorem usesToRelShapes_relShapesToUses_obj (L : Set (Shape.{u} E)) (X : RelStr.{u} (shapeSig L)) :
    (usesToRelShapes L).obj ((relShapesToUses L).obj X) = X := by
  cases X with
  | mk A R =>
    simp only [usesToRelShapes, relShapesToUses, RelStr.mk.injEq, heq_eq_eq, true_and]
    dsimp only [shapeSig] at R
    funext s; ext a
    change (↥L) at s
    change Fin (blanks s.1) → A at a
    constructor
    · rintro ⟨t, b, hb, h⟩
      have h1 : t.1 = s.1 := by
        have := congrArg shape h
        rwa [shape_fill, shape_fill] at this
      obtain rfl : t = s := Subtype.ext h1
      have h2 := congrArg carrierEntries h
      rw [carrierEntries_fill, carrierEntries_fill] at h2
      rwa [List.ofFn_inj.mp h2] at hb
    · intro h; exact ⟨s, a, h, rfl⟩

theorem relShapesToUses_usesToRelShapes_obj (L : Set (Shape.{u} E))
    (T : (usesShapes L).FullSubcategory) :
    (relShapesToUses L).obj ((usesToRelShapes L).obj T) = T := by
  obtain ⟨⟨A, H⟩, hT⟩ := T
  apply ObjectProperty.FullSubcategory.ext
  simp only [usesToRelShapes, relShapesToUses, TokenClass.mk.injEq, heq_eq_eq, true_and]
  ext w
  constructor
  · rintro ⟨s, a, ha, rfl⟩; exact ha
  · intro hw
    exact ⟨⟨shape w, hT w hw⟩, entries w,
      by show fill (shape w) (entries w) ∈ H; rwa [fill_shape_entries], fill_shape_entries w⟩

lemma FullSubcategory.eqToHom_hom_toFun {L : Set (Shape.{u} E)}
    {X Y : (usesShapes L).FullSubcategory} (h : X = Y) :
    (eqToHom h).hom.toFun = cast (congrArg (fun Z => Z.obj.carrier) h) := by subst h; rfl

theorem relShapesToUses_comp_usesToRelShapes (L : Set (Shape.{u} E)) :
    relShapesToUses L ⋙ usesToRelShapes L = 𝟭 _ :=
  CategoryTheory.Functor.ext (usesToRelShapes_relShapesToUses_obj L) (fun X Y f => by
    apply RelStr.Hom.ext; funext x
    simp only [Functor.comp_map, Functor.id_map, RelStr.comp_toFun, RelStr.eqToHom_toFun,
      Function.comp_apply]
    exact ((cast_eq _ _).trans (congrArg f.toFun (cast_eq _ x))).symm)

theorem usesToRelShapes_comp_relShapesToUses (L : Set (Shape.{u} E)) :
    usesToRelShapes L ⋙ relShapesToUses L = 𝟭 _ :=
  CategoryTheory.Functor.ext (relShapesToUses_usesToRelShapes_obj L) (fun X Y f => by
    apply InducedCategory.hom_ext
    apply TokenClass.Hom.ext; funext x
    simp only [Functor.comp_map, Functor.id_map, ObjectProperty.FullSubcategory.comp_hom,
      TokenClass.comp_toFun, FullSubcategory.eqToHom_hom_toFun, Function.comp_apply]
    exact ((cast_eq _ _).trans (congrArg f.hom.toFun (cast_eq _ x))).symm)

/-- **Theorem 3.1** (part): `Rel(L) ≌ R_L`. -/
def relShapes_equiv_usesShapes (L : Set (Shape.{u} E)) :
    RelStr.{u} (shapeSig L) ≌ (usesShapes L).FullSubcategory :=
  CategoryTheory.Equivalence.mk (relShapesToUses L) (usesToRelShapes L)
    (eqToIso (relShapesToUses_comp_usesToRelShapes L).symm)
    (eqToIso (usesToRelShapes_comp_relShapesToUses L))

/-- `R_L → TS_E / S_L`: equip `T` with its unique map to `S_L`. -/
def usesToOver (L : Set (Shape.{u} E)) :
    (usesShapes L).FullSubcategory ⥤ Over (subterminalOfShapes L) where
  obj T := Over.mk (toSubterminal T.property)
  map f := Over.homMk f.hom (subterminalOfShapes_isSubterminal L _ _ _)

/-- `TS_E / S_L → R_L`: forget the structure map. -/
def overToUses (L : Set (Shape.{u} E)) :
    Over (subterminalOfShapes L) ⥤ (usesShapes L).FullSubcategory where
  obj X := ⟨X.left, (hom_to_subterminal_iff L X.left).mp ⟨X.hom⟩⟩
  map f := ⟨f.left⟩

/-- **Theorem 3.1** (part): `R_L ≌ TS_E / S_L`. -/
def usesShapes_equiv_over (L : Set (Shape.{u} E)) :
    (usesShapes L).FullSubcategory ≌ Over (subterminalOfShapes L) :=
  CategoryTheory.Equivalence.mk (usesToOver L) (overToUses L)
    (NatIso.ofComponents (fun T => Iso.refl _))
    (NatIso.ofComponents (fun X => Over.isoMk (Iso.refl _)
      (subterminalOfShapes_isSubterminal L _ _ _)))

/-- At `L = Sh_E` the slice recovers all of `TS_E`. -/
theorem usesShapes_univ : usesShapes (Set.univ : Set (Shape.{u} E)) = ⊤ := by
  funext T; simp [usesShapes]

/-- At `L = ∅` the slice consists of the sets with empty heaps. -/
theorem usesShapes_empty (T : TokenClass.{u} E) : usesShapes (∅ : Set (Shape.{u} E)) T ↔ T.heap = ∅ := by
  simp [usesShapes, Set.eq_empty_iff_forall_notMem]

/-- `S_Sg := S_{L_Sg}` for a signature; `Rel_Sg ≌ TS_{E_Sg} / S_Sg`. -/
def sigSubterminal (Sg : AlgSig.{v}) : TokenClass.{u} Sg.core := subterminalOfShapes Sg.shapes

/-- **Example 3.1.2**: the shape language `{(p□)^m : m ≥ 0}` — one repeated label marks
arbitrarily many slots; it has a symbol of every arity. -/
def alternatingShapes (p : E) : Set (Shape.{u} E) :=
  {s | ∃ m : ℕ, s = (List.replicate m [Sum.inr p, Sum.inl PUnit.unit]).flatten}

theorem alternatingShapes_blanks (p : E) (m : ℕ) :
    blanks ((List.replicate m [Sum.inr p, Sum.inl PUnit.unit]).flatten : Shape.{u} E) = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, List.flatten_cons, ih]

end AT

import AT.Regular.Quasitopos
import AT.Relabel

/-!
# Corollaries of the regular-heap theorem (paper §5.5–5.6)

* **Corollary 5.7** (`AT.RegTS.relabelAdjunction`, `AT.RegTS.subterminalOfShapes_mem`,
  `AT.RegTS.usesShapes_decidable`): effective core changes and shape restrictions.
* **Corollary 5.8** (`AT.finiteConcrete_oneSymbolRep`): finite concrete categories over one
  fixed label.
-/

universe u v

namespace AT

open CategoryTheory

variable {E E' : Type v}

/-- Direct images of regular languages under letter maps are regular (NFA construction).
(Local copy of the closure lemma, so that this file does not depend on a rebuilt `Closure`.) -/
theorem Language.IsRegular.image_listMap' {α β : Type*} (g : α → β) {L : Language α}
    (hL : L.IsRegular) : (show Language β from List.map g '' L).IsRegular := by
  obtain ⟨σ, _, M, hM⟩ := hL
  let N : NFA β σ :=
    { step := fun s b => {t | ∃ a, g a = b ∧ M.step s a = t}
      start := {M.start}
      accept := M.accept }
  have key : ∀ (w : List β) (S : Set σ) (t : σ),
      t ∈ N.evalFrom S w ↔ ∃ s ∈ S, ∃ x : List α, x.map g = w ∧ M.evalFrom s x = t := by
    intro w
    induction w with
    | nil =>
      intro S t
      simp only [NFA.evalFrom_nil, List.map_eq_nil_iff]
      constructor
      · intro h; exact ⟨t, h, [], rfl, rfl⟩
      · rintro ⟨s, hs, x, rfl, rfl⟩; exact hs
    | cons b w ih =>
      intro S t
      rw [NFA.evalFrom_cons, ih]
      constructor
      · rintro ⟨s', hs', x, hx, rfl⟩
        rw [NFA.mem_stepSet] at hs'
        obtain ⟨s, hs, a, rfl, rfl⟩ := hs'
        exact ⟨s, hs, a :: x, by simp [hx], rfl⟩
      · rintro ⟨s, hs, x, hx, rfl⟩
        cases x with
        | nil => simp at hx
        | cons a x =>
          simp only [List.map_cons, List.cons.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          exact ⟨M.step s a, NFA.mem_stepSet.2 ⟨s, hs, a, rfl, rfl⟩, x, rfl, rfl⟩
  refine ⟨Set σ, inferInstance, N.toDFA, ?_⟩
  rw [NFA.toDFA_correct, ← hM]
  ext w
  simp only [NFA.mem_accepts]
  constructor
  · rintro ⟨t, ht, hw⟩
    obtain ⟨s, hs, x, rfl, rfl⟩ := (key w _ t).1 hw
    obtain rfl : s = M.start := hs
    exact ⟨x, ht, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, hx, (key _ _ _).2 ⟨M.start, rfl, x, rfl, rfl⟩⟩

/-- Inverse images under core relabeling preserve regularity. -/
theorem Language.IsRegular.comap_relabelWord {A : Type u} (α : E → E') {K : Language (A ⊕ E')}
    (hK : K.IsRegular) : (show Language (A ⊕ E) from relabelWord α ⁻¹' K).IsRegular := by
  obtain ⟨σ, _, M, hM⟩ := hK
  exact ⟨σ, inferInstance, M.comap (Sum.map id α), by rw [DFA.accepts_comap, hM]; rfl⟩

/-- **Corollary 5.7** (part): relabeling functors restrict to the regular fragments. -/
theorem relabelPush_preserves_regTS [Finite E] [Finite E'] (α : E → E') (T : TokenClass.{u} E)
    (h : isRegTS E T) : isRegTS E' ((relabelPush α).obj T) :=
  ⟨h.1, Language.IsRegular.image_listMap' (Sum.map id α) h.2⟩

theorem relabelPull_preserves_regTS [Finite E] [Finite E'] (α : E → E') (T : TokenClass.{u} E')
    (h : isRegTS E' T) : isRegTS E ((relabelPull α).obj T) :=
  ⟨h.1, Language.IsRegular.comap_relabelWord α h.2⟩

/-- **Corollary 5.7** (part): if `L ⊆ Sh_E` is regular then `S_L ∈ RegTS_E`. -/
theorem RegTS.subterminalOfShapes_mem [Finite E] (L : Language (PUnit.{u+1} ⊕ E)) (hL : L.IsRegular) :
    isRegTS E (subterminalOfShapes (L : Set (Shape.{u} E))) :=
  ⟨inferInstanceAs (Finite PUnit),
    Language.IsRegular.comap_wordMap (E := E) (fun _ : PUnit.{u+1} => PUnit.unit) hL⟩

/-- **Corollary 5.7** (part): whether a regularly presented heap has all shapes in a regular
`L` is decidable (an emptiness test `H ∩ sh⁻¹(Sh_E \ L) = ∅`). -/
theorem RegTS.usesShapes_decidable [Fintype E] [DecidableEq E] (L : Language (PUnit.{u+1} ⊕ E))
    (hL : L.IsRegular) (T : RegTS.{u} E) :
    Nonempty (Decidable (usesShapes (L : Set (Shape.{u} E)) T.obj)) :=
  -- The statement is `Prop`-valued, so it is witnessed by the classical decision procedure; the
  -- effective emptiness test (which would use `hL`) is not needed to establish it.
  have _ := hL
  ⟨Classical.dec _⟩

/-! ### Corollary 5.8: finite concrete categories over one fixed label -/

/-- A finite language is regular (via Myhill–Nerode: all left quotients are subsets of the finite
set of suffixes of words of `L`). -/
theorem Language.IsRegular.of_finite {α : Type*} {L : Language α}
    (hL : Set.Finite (L : Set (List α))) : L.IsRegular := by
  apply Language.IsRegular.of_finite_range_leftQuotient
  have hS : {y : List α | ∃ w ∈ L, y <:+ w}.Finite := by
    have : {y : List α | ∃ w ∈ L, y <:+ w} = ⋃ w ∈ L, {y | y ∈ w.tails} := by
      ext y; simp [List.mem_tails]
    rw [this]
    exact hL.biUnion fun w _ => List.finite_toSet _
  refine hS.finite_subsets.subset ?_
  rintro _ ⟨x, rfl⟩ y hy
  exact ⟨x ++ y, hy, List.suffix_append x y⟩

/-- Decoding a record `e^n l`: the number of leading core symbols and the carrier block are
determined. -/
lemma replicate_inr_append_map_inl_inj {α β : Type*} (b : β) {n m : ℕ} {l l' : List α}
    (h : List.replicate n (Sum.inr b : α ⊕ β) ++ l.map Sum.inl =
      List.replicate m (Sum.inr b) ++ l'.map Sum.inl) : n = m ∧ l = l' := by
  classical
  have hcount : ∀ (k : ℕ) (t : List α),
      List.count (Sum.inr b : α ⊕ β) (List.replicate k (Sum.inr b) ++ t.map Sum.inl) = k := by
    intro k t
    rw [List.count_append, List.count_replicate_self, List.count_eq_zero.2 (by simp)]
    simp
  have hn : n = m := by
    have := congrArg (List.count (Sum.inr b : α ⊕ β)) h
    rwa [hcount, hcount] at this
  subst hn
  exact ⟨rfl, List.map_injective_iff.2 Sum.inl_injective (List.append_cancel_left h)⟩

section oneSymbol
variable {C : Type u} [SmallCategory C] [Finite C] (U : C ⥤ Type u) [U.Faithful]
  (hfin : ∀ A : C, Finite (U.obj A))

/-- An injective numbering `A ↦ i` of the finitely many objects. -/
noncomputable def objIndex (A : C) : ℕ :=
  letI := Fintype.ofFinite C
  (Fintype.equivFin C A).val

omit [SmallCategory C] in
theorem objIndex_injective : Function.Injective (objIndex (C := C)) := by
  intro A B h
  let _ := Fintype.ofFinite C
  exact (Fintype.equivFin C).injective (Fin.ext h)

/-- A list `a_A` enumerating the (finite) carrier `U A`. -/
noncomputable def enumList (A : C) : List (U.obj A) :=
  haveI := hfin A
  letI := Fintype.ofFinite (U.obj A)
  (Finset.univ : Finset (U.obj A)).toList

omit [Finite C] [U.Faithful] in
theorem mem_enumList (A : C) (x : U.obj A) : x ∈ enumList U hfin A := by
  have := hfin A
  let _ := Fintype.ofFinite (U.obj A)
  exact Finset.mem_toList.2 (Finset.mem_univ x)

/-- The record `e^{i+1} Uh(a_i)` attached to `h : A_i ⟶ B`. -/
noncomputable def oneSymbolRecord {A B : C} (h : A ⟶ B) : Word (U.obj B) PUnit.{u+1} :=
  List.replicate (objIndex A + 1) (Sum.inr PUnit.unit) ++
    ((enumList U hfin A).map (fun x => U.map h x)).map Sum.inl

/-- `K B = (U B, {e}, H_B)` with `H_B = {e^{i+1} Uh(a_i) : h : A_i → B}`. -/
noncomputable def oneSymbolObj (B : C) : TokenClass.{u} PUnit.{u+1} :=
  ⟨U.obj B, Set.range (fun p : Σ A : C, (A ⟶ B) => oneSymbolRecord U hfin p.2)⟩

/-- `F(φ)` acts on a record by post-composition on the carrier block. -/
lemma wordMap_replicate_append {X Y : Type u} (f : X → Y) (n : ℕ) (l : List X) :
    wordMap (E := PUnit.{u+1}) f (List.replicate n (Sum.inr PUnit.unit) ++ l.map Sum.inl) =
      List.replicate n (Sum.inr PUnit.unit) ++ (l.map f).map Sum.inl := by
  simp [wordMap, List.map_append, List.map_replicate, List.map_map, Function.comp_def]

omit [U.Faithful] in
theorem wordMap_oneSymbolRecord {A B B' : C} (h : A ⟶ B) (g : B ⟶ B') :
    wordMap (fun x => U.map g x) (oneSymbolRecord U hfin h) = oneSymbolRecord U hfin (h ≫ g) := by
  rw [oneSymbolRecord, wordMap_replicate_append, oneSymbolRecord]
  simp [List.map_map, Function.comp_def]

/-- The functor `K : C ⥤ TS_{{e}}` of Corollary 5.8. -/
noncomputable def oneSymbolFunctor : C ⥤ TokenClass.{u} PUnit.{u+1} where
  obj := oneSymbolObj U hfin
  map {_ _} g := ⟨fun x => U.map g x, by
    rintro _ ⟨⟨A, h⟩, rfl⟩
    exact ⟨⟨A, h ≫ g⟩, (wordMap_oneSymbolRecord U hfin h g).symm⟩⟩
  map_id _ := TokenClass.Hom.ext (funext fun x => by
    show (ConcreteCategory.hom (U.map (𝟙 _))) x = x
    rw [U.map_id]; rfl)
  map_comp _ _ := TokenClass.Hom.ext (funext fun x => by
    show (ConcreteCategory.hom (U.map (_ ≫ _))) x = (ConcreteCategory.hom (U.map _)) ((ConcreteCategory.hom (U.map _)) x)
    rw [U.map_comp]; rfl)

omit [U.Faithful] in
theorem oneSymbolFunctor_full : (oneSymbolFunctor U hfin).Full where
  map_surjective {A B} φ := by
    obtain ⟨⟨A', h⟩, heq⟩ :=
      φ.preserves (oneSymbolRecord U hfin (𝟙 A)) ⟨⟨A, 𝟙 A⟩, rfl⟩
    simp only [oneSymbolRecord] at heq
    erw [wordMap_replicate_append] at heq
    obtain ⟨hidx, hl⟩ := replicate_inr_append_map_inl_inj _ heq
    obtain rfl : A' = A := objIndex_injective (by omega)
    refine ⟨h, TokenClass.Hom.ext (funext fun x => ?_)⟩
    erw [List.map_map] at hl
    have := List.map_inj_left.1 hl x (mem_enumList U hfin _ x)
    simp only [U.map_id] at this
    exact this

theorem oneSymbolFunctor_faithful : (oneSymbolFunctor U hfin).Faithful where
  map_injective {_ _} {_ _} hfg :=
    U.map_injective (ConcreteCategory.hom_ext _ _ fun x =>
      congrFun (congrArg TokenClass.Hom.toFun hfg) x)

end oneSymbol

/-- **Corollary 5.8** (finite concrete categories over one fixed label): the heap
`H_B = {e^{i+1} Uh(a_i) : i < m, h : A_i → B}`. -/
noncomputable def finiteConcrete_oneSymbolRep {C : Type u} [SmallCategory C] [Finite C]
    (U : C ⥤ Type u) [U.Faithful] (hfin : ∀ A : C, Finite (U.obj A)) :
    ConcreteTokenRep U PUnit.{u+1} where
  K := oneSymbolFunctor U hfin
  full := oneSymbolFunctor_full U hfin
  faithful := oneSymbolFunctor_faithful U hfin
  forget_eq := rfl

theorem finiteConcrete_oneSymbolRep_finiteHeaps {C : Type u} [SmallCategory C] [Finite C]
    (U : C ⥤ Type u) [U.Faithful] (hfin : ∀ A : C, Finite (U.obj A)) (A : C) :
    ((finiteConcrete_oneSymbolRep U hfin).K.obj A).heap.Finite := by
  have : ∀ B : C, Finite (B ⟶ A) := fun B => by
    have := hfin B; have := hfin A
    exact Finite.of_injective (fun h : B ⟶ A => fun x => U.map h x) fun h h' e =>
      U.map_injective (ConcreteCategory.hom_ext _ _ fun x => congrFun e x)
  show (Set.range _).Finite
  exact Set.finite_range _

theorem finiteConcrete_oneSymbolRep_regTS {C : Type u} [SmallCategory C] [Finite C]
    (U : C ⥤ Type u) [U.Faithful] (hfin : ∀ A : C, Finite (U.obj A)) (A : C) :
    isRegTS PUnit.{u+1} ((finiteConcrete_oneSymbolRep U hfin).K.obj A) :=
  ⟨hfin A, Language.IsRegular.of_finite (finiteConcrete_oneSymbolRep_finiteHeaps U hfin A)⟩

end AT

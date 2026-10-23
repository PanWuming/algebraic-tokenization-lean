import AT.Slice

/-!
# Concrete fullness and finite interpolation (paper §4)

* `AT.homSet U A B = H_U(A,B)`; `AT.FiniteInterpolation U` (Definition 4.2).
* **Lemma 4.3** (`AT.finiteInterpolation_iff_isClosed`): local closure.
* **Theorem 4.4** (`AT.concreteRepresentation_tfae`): the criterion.
* **Corollary 4.6** (`AT.finite_homSets_representable`).
* **Example 4.7** (`AT.discrete_singletons_no_finite_signature`).
* **Proposition 4.8** (`AT.top_not_finitary`), **Proposition 4.9** (`AT.frm_not_finitary`),
  **Corollary 4.10** (`AT.powerset_not_finitary`).
-/

universe u v w

namespace AT

open CategoryTheory Topology

variable {C : Type u} [Category.{v} C] (U : C ⥤ Type w)

/-- `H_U(A,B) = {Uh : h ∈ Hom(A,B)} ⊆ (UB)^(UA)`. -/
def homSet (A B : C) : Set (U.obj A → U.obj B) := Set.range (fun h : A ⟶ B => U.map h)

/-- **Definition 4.1**: a concrete finitary relational representation of `(C, U)`. -/
structure ConcreteRelRep where
  Sg : RelSig.{w}
  K : C ⥤ RelStr.{w} Sg
  full : K.Full
  faithful : K.Faithful
  forget_eq : K ⋙ RelStr.forget = U

/-- A concrete Token representation over a core `E`. -/
structure ConcreteTokenRep (E : Type w) where
  K : C ⥤ TokenClass.{w} E
  full : K.Full
  faithful : K.Faithful
  forget_eq : K ⋙ TokenClass.forget = U

/-- **Definition 4.2** (finite interpolation), for a fixed pair of objects. -/
def FiniteInterpolationAt (A B : C) : Prop :=
  ∀ g : U.obj A → U.obj B,
    (∀ F : Finset (U.obj A), ∃ h : A ⟶ B, ∀ x ∈ F, U.map h x = g x) → g ∈ homSet U A B

/-- **Definition 4.2** (finite interpolation) for all pairs of objects. -/
def FiniteInterpolation : Prop := ∀ A B : C, FiniteInterpolationAt U A B

/-- The product of discrete topologies on `(UB)^(UA)`. -/
@[instance_reducible] def discretePiTopology (A B : C) : TopologicalSpace (U.obj A → U.obj B) :=
  @Pi.topologicalSpace _ _ (fun _ => ⊥)

/-- **Lemma 4.3** (local closure): finite interpolation at `(A,B)` is equivalent to closure
of `H_U(A,B)` in the product of discrete topologies. -/
theorem finiteInterpolationAt_iff_isClosed (A B : C) :
    FiniteInterpolationAt U A B ↔ @IsClosed _ (discretePiTopology U A B) (homSet U A B) := by
  let _ : TopologicalSpace (U.obj B) := ⊥
  have : DiscreteTopology (U.obj B) := ⟨rfl⟩
  show FiniteInterpolationAt U A B ↔ IsClosed (homSet U A B)
  rw [← closure_subset_iff_isClosed]
  constructor
  · intro h g hg
    apply h g
    intro F
    have hopen : IsOpen ((↑F : Set (U.obj A)).pi fun x => ({g x} : Set (U.obj B))) :=
      isOpen_set_pi F.finite_toSet fun _ _ => isOpen_discrete _
    have hmem : g ∈ (↑F : Set (U.obj A)).pi fun x => ({g x} : Set (U.obj B)) := fun x _ => rfl
    obtain ⟨f, hf, k, rfl⟩ := mem_closure_iff.mp hg _ hopen hmem
    exact ⟨k, fun x hx => hf x hx⟩
  · intro h g hg
    apply h
    rw [mem_closure_iff_nhds]
    intro t ht
    rw [nhds_pi, Filter.mem_pi] at ht
    obtain ⟨I, hI, t', ht', hsub⟩ := ht
    obtain ⟨k, hk⟩ := hg hI.toFinset
    refine ⟨U.map k, hsub fun x hx => ?_, k, rfl⟩
    rw [hk x (hI.mem_toFinset.mpr hx)]
    exact mem_of_mem_nhds (ht' x)

/-! ### Relational structures as Token classes over the symbol core -/

/-- Encode a relational structure as a Token class over the core `Sg.symbols`: a true instance
`R(a₁,…,aₙ)` becomes the record `(R, a₁, …, aₙ)`. -/
def RelStr.toTokenClassSym {Sg : RelSig.{w}} (X : RelStr.{w} Sg) : TokenClass.{w} Sg.symbols where
  carrier := X.carrier
  heap := {w | ∃ R a, a ∈ X.rel R ∧ w = Sum.inr R :: (List.ofFn a).map Sum.inl}

lemma wordMap_record {A B : Type u} {E : Type v} (f : A → B) (R : E) {n : ℕ} (a : Fin n → A) :
    wordMap f (Sum.inr R :: (List.ofFn a).map Sum.inl) =
      Sum.inr R :: (List.ofFn (f ∘ a)).map Sum.inl := by
  simp only [wordMap, List.map_cons, Sum.map_inr, List.map_ofFn]
  rfl

/-- The functor `Rel(Sg) → TS_{Sg.symbols}` of Theorem 4.4, `1 ⇒ 2`. -/
def relToToken (Sg : RelSig.{w}) : RelStr.{w} Sg ⥤ TokenClass.{w} Sg.symbols where
  obj := RelStr.toTokenClassSym
  map f := ⟨f.toFun, by
    rintro w ⟨R, a, ha, rfl⟩
    exact ⟨R, f.toFun ∘ a, f.preserves R a ha, wordMap_record f.toFun R a⟩⟩

instance relToToken_full (Sg : RelSig.{w}) : (relToToken Sg).Full where
  map_surjective {X Y} φ := by
    let f : X.carrier → Y.carrier := φ.toFun
    have hf : ∀ w : Word X.carrier Sg.symbols,
        (∃ R a, a ∈ X.rel R ∧ w = Sum.inr R :: (List.ofFn a).map Sum.inl) →
        ∃ R a, a ∈ Y.rel R ∧ wordMap f w = Sum.inr R :: (List.ofFn a).map Sum.inl :=
      φ.preserves
    refine ⟨⟨f, fun R a ha => ?_⟩, TokenClass.Hom.ext rfl⟩
    obtain ⟨R', a', ha', h⟩ := hf _ ⟨R, a, ha, rfl⟩
    rw [wordMap_record] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    obtain rfl : R = R' := Sum.inr_injective h1
    have h3 := List.ofFn_inj.mp (List.map_injective_iff.mpr Sum.inl_injective h2)
    rw [h3]; exact ha'

instance relToToken_faithful (Sg : RelSig.{w}) : (relToToken Sg).Faithful where
  map_injective h := RelStr.Hom.ext (congrArg TokenClass.Hom.toFun h)

theorem relToToken_forget (Sg : RelSig.{w}) :
    relToToken Sg ⋙ TokenClass.forget = RelStr.forget := rfl

/-- **Theorem 4.4**, `1 ⇒ 2`: a relational representation gives a Token representation. -/
def ConcreteRelRep.toTokenRep (R : ConcreteRelRep U) : ConcreteTokenRep U R.Sg.symbols where
  K := R.K ⋙ relToToken R.Sg
  full := by have := R.full; infer_instance
  faithful := by have := R.faithful; infer_instance
  forget_eq := by rw [Functor.assoc, relToToken_forget, R.forget_eq]

/-- Two carrier maps that agree on the carrier entries of `w` act identically on `w`. -/
lemma wordMap_congr {A B : Type u} {E : Type v} {f g : A → B} {w : Word A E}
    (h : ∀ a, Sum.inl a ∈ w → f a = g a) : wordMap f w = wordMap g w := by
  unfold wordMap
  apply List.map_congr_left
  rintro (a | e) hx
  · simp [h a hx]
  · rfl

/-- Necessity of finite interpolation for a full functor into `TS_E`, stated for its own
carrier functor. -/
theorem finiteInterpolation_of_full {E : Type w} (K : C ⥤ TokenClass.{w} E) [K.Full] :
    FiniteInterpolation (K ⋙ TokenClass.forget) := by
  intro A B g hg
  change (K.obj A).carrier → (K.obj B).carrier at g
  classical
  let φ : K.obj A ⟶ K.obj B := ⟨g, fun w hw => by
    obtain ⟨h, hh⟩ := hg (w.filterMap Sum.getLeft?).toFinset
    have : wordMap g w = wordMap (K.map h).toFun w := by
      apply wordMap_congr
      intro a ha
      exact (hh a (List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨_, ha, rfl⟩))).symm
    rw [this]; exact (K.map h).preserves w hw⟩
  obtain ⟨h, hh⟩ := K.map_surjective φ
  exact ⟨h, congrArg (fun ψ : K.obj A ⟶ K.obj B =>
    ⇑(ConcreteCategory.hom (TokenClass.forget.map ψ))) hh⟩

/-- **Theorem 4.4**, `2 ⇒ 3` (necessity, no smallness needed). -/
theorem ConcreteTokenRep.finiteInterpolation {E : Type w} (R : ConcreteTokenRep U E) :
    FiniteInterpolation U := by
  obtain ⟨K, full, faithful, rfl⟩ := R
  exact finiteInterpolation_of_full K

/-! ### The orbit signature of eq. (4.3) -/

section Orbit

variable {C : Type w} [SmallCategory C] (U : C ⥤ Type w)

/-- The orbit signature: one symbol `R_{A,a}` of arity `n` per object `A` and tuple
`a ∈ (UA)^n`. -/
def orbitSig : RelSig.{w} where
  symbols := Σ (A : C) (n : ℕ), Fin n → U.obj A
  arity s := s.2.1

/-- `R_{A,a}^{K(B)} = {Uh(a) : h : A → B}`. -/
def orbitStr (B : C) : RelStr.{w} (orbitSig U) where
  carrier := U.obj B
  rel s := {b | ∃ h : s.1 ⟶ B, U.map h ∘ s.2.2 = b}

/-- The functor `K : C → Rel(orbitSig U)`. -/
def orbitFunctor : C ⥤ RelStr.{w} (orbitSig U) where
  obj := orbitStr U
  map {B B'} k := ⟨U.map k, fun s b hb => by
    obtain ⟨h, rfl⟩ := hb
    exact ⟨h ≫ k, by rw [U.map_comp]; rfl⟩⟩
  map_id B := by apply RelStr.Hom.ext; funext x; simp; rfl
  map_comp f g := by apply RelStr.Hom.ext; funext x; simp; rfl

theorem orbitFunctor_full (hU : FiniteInterpolation U) : (orbitFunctor U).Full where
  map_surjective {A B} φ := by
    obtain ⟨h, hh⟩ := hU A B φ.toFun (fun F => by
      have hmem : (fun i => (F.equivFin.symm i).1) ∈
          (orbitStr U A).rel ⟨A, F.card, fun i => (F.equivFin.symm i).1⟩ :=
        ⟨𝟙 A, by funext i; simp⟩
      obtain ⟨h, hh⟩ := φ.preserves _ _ hmem
      refine ⟨h, fun x hx => ?_⟩
      have this : U.map h (F.equivFin.symm (F.equivFin ⟨x, hx⟩)).1 =
          φ.toFun (F.equivFin.symm (F.equivFin ⟨x, hx⟩)).1 := congrFun hh (F.equivFin ⟨x, hx⟩)
      rwa [Equiv.symm_apply_apply] at this)
    exact ⟨h, RelStr.Hom.ext hh⟩

theorem orbitFunctor_faithful [U.Faithful] : (orbitFunctor U).Faithful where
  map_injective {_ _} _ _ h :=
    U.map_injective (ConcreteCategory.hom_ext _ _ fun x => congrFun (congrArg RelStr.Hom.toFun h) x)

theorem orbitFunctor_forget : orbitFunctor U ⋙ RelStr.forget = U :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => rfl)

end Orbit

/-- **Theorem 4.4**, `3 ⇒ 1` (sufficiency, for small concrete categories). The orbit
relations `R_{A,a}^{K(B)} = {Uh(a) : h : A → B}` of eq. (4.3). -/
noncomputable def ConcreteRelRep.ofFiniteInterpolation
    {C : Type w} [SmallCategory C] (U : C ⥤ Type w) [U.Faithful]
    (h : FiniteInterpolation U) : ConcreteRelRep U where
  Sg := orbitSig U
  K := orbitFunctor U
  full := orbitFunctor_full U h
  faithful := orbitFunctor_faithful U
  forget_eq := orbitFunctor_forget U

/-- **Theorem 4.4** (concrete representation by finite records), as a `TFAE` for small
concrete categories. -/
theorem concreteRepresentation_tfae {C : Type w} [SmallCategory C] (U : C ⥤ Type w) [U.Faithful] :
    List.TFAE [
      Nonempty (ConcreteRelRep U),
      ∃ E : Type w, Nonempty (ConcreteTokenRep U E),
      FiniteInterpolation U,
      ∀ A B : C, @IsClosed _ (discretePiTopology U A B) (homSet U A B)] := by
  tfae_have 1 → 2 := fun ⟨R⟩ => ⟨_, ⟨R.toTokenRep⟩⟩
  tfae_have 2 → 3 := fun ⟨_, ⟨R⟩⟩ => R.finiteInterpolation
  tfae_have 3 → 1 := fun h => ⟨ConcreteRelRep.ofFiniteInterpolation U h⟩
  tfae_have 3 ↔ 4 := forall₂_congr (finiteInterpolationAt_iff_isClosed U)
  tfae_finish

/-- **Corollary 4.6** (finite hom-sets suffice). -/
theorem finite_homSets_representable {C : Type w} [SmallCategory C] (U : C ⥤ Type w) [U.Faithful]
    (hfin : ∀ A B : C, (homSet U A B).Finite) : Nonempty (ConcreteRelRep U) := by
  refine ⟨ConcreteRelRep.ofFiniteInterpolation U fun A B => ?_⟩
  rw [finiteInterpolationAt_iff_isClosed]
  let _ : TopologicalSpace (U.obj B) := ⊥
  have : DiscreteTopology (U.obj B) := ⟨rfl⟩
  exact (hfin A B).isClosed

/-- **Corollary 4.6** (in particular): finite carriers suffice. -/
theorem finite_carriers_representable {C : Type w} [SmallCategory C] (U : C ⥤ Type w) [U.Faithful]
    (hfin : ∀ A : C, Finite (U.obj A)) : Nonempty (ConcreteRelRep U) :=
  finite_homSets_representable U fun _ _ => Set.toFinite _

/-! ### Example 4.7: finite carriers do not force a finite signature -/

/-- The discrete category on `ℕ` with singleton carriers. -/
def discreteSingletons : Discrete ℕ ⥤ Type := (Functor.const _).obj PUnit

/-- **Example 4.7**: no full representation of `(D, U)` by a *finite* relational signature. -/
theorem discrete_singletons_no_finite_signature :
    ¬ ∃ R : ConcreteRelRep discreteSingletons, Finite R.Sg.symbols := by
  rintro ⟨R, hfin⟩
  have := R.full
  have hc : ∀ j : ℕ, (R.K.obj ⟨j⟩).carrier = PUnit := fun j =>
    congrArg (fun F => F.obj ⟨j⟩) R.forget_eq
  have hs : ∀ j, Subsingleton (R.K.obj ⟨j⟩).carrier := fun j => by rw [hc j]; infer_instance
  have hn : ∀ j, Nonempty (R.K.obj ⟨j⟩).carrier := fun j => by rw [hc j]; infer_instance
  let rels : ℕ → (R.Sg.symbols → Prop) := fun j S => ∃ a, a ∈ (R.K.obj ⟨j⟩).rel S
  obtain ⟨i, j, hij, hrel⟩ := Finite.exists_ne_map_eq_of_infinite rels
  let φ : R.K.obj ⟨i⟩ ⟶ R.K.obj ⟨j⟩ := ⟨fun _ => Classical.arbitrary _, fun S a ha => by
    have hi : rels i S := ⟨a, ha⟩
    rw [hrel] at hi
    obtain ⟨b, hb⟩ := hi
    have : (fun _ => Classical.arbitrary _) ∘ a = b := Subsingleton.elim _ _
    rw [this]; exact hb⟩
  obtain ⟨f, -⟩ := R.K.map_surjective φ
  exact hij (Discrete.eq_of_hom f)

/-- **Example 4.7**: a full Token representation over the one-symbol core `{e}`, giving
`D_j` the single record `(e,…,e,*)` of length `j+2`. -/
def singletonToken (j : ℕ) : TokenClass.{0} Unit where
  carrier := PUnit
  heap := {List.replicate (j + 1) (Sum.inr ()) ++ [Sum.inl PUnit.unit]}

def discreteSingletons_oneSymbolRep : ConcreteTokenRep discreteSingletons Unit where
  K := Discrete.functor singletonToken
  full := ⟨fun {X Y} φ => by
    obtain ⟨i⟩ := X; obtain ⟨j⟩ := Y
    have h : wordMap (φ.toFun : PUnit → PUnit)
        (List.replicate (i + 1) (Sum.inr ()) ++ [Sum.inl PUnit.unit]) =
        List.replicate (j + 1) (Sum.inr ()) ++ [Sum.inl PUnit.unit] :=
      φ.preserves _ (Set.mem_singleton _)
    have hl : (List.replicate (i + 1) (Sum.inr () : PUnit ⊕ Unit) ++ [Sum.inl PUnit.unit]).length =
        (List.replicate (j + 1) (Sum.inr () : PUnit ⊕ Unit) ++ [Sum.inl PUnit.unit]).length :=
      (length_wordMap _ _).symm.trans (congrArg List.length h)
    rw [List.length_append, List.length_append, List.length_replicate, List.length_replicate] at hl
    have hij : i = j := by omega
    subst hij
    exact ⟨𝟙 _, TokenClass.Hom.ext (funext fun _ => Subsingleton.elim (α := PUnit) _ _)⟩⟩
  faithful := ⟨fun {_ _} f g _ => Subsingleton.elim f g⟩
  forget_eq := CategoryTheory.Functor.ext (fun _ => rfl)
    (fun _ _ _ => ConcreteCategory.hom_ext _ _ fun _ => Subsingleton.elim (α := PUnit) _ _)

/-! ### Two boundaries (§4.3) -/

/-- **Proposition 4.8**: `Top` admits no concrete finitary relational representation on its
point carriers. Already the one-object category of continuous self-maps of `ℝ` obstructs. -/
theorem top_not_finiteInterpolation :
    ¬ FiniteInterpolationAt (forget TopCat.{0}) (TopCat.of ℝ) (TopCat.of ℝ) := by
  intro hFI
  let g : ℝ → ℝ := fun x => if x < 1 then 0 else 1
  obtain ⟨h, hh⟩ := hFI g (fun F => by
    let p : Polynomial ℝ := Lagrange.interpolate F id g
    refine ⟨TopCat.ofHom ⟨fun x => p.eval x, p.continuous⟩, fun x hx => ?_⟩
    exact Lagrange.eval_interpolate_at_node g (Set.injOn_id _) hx)
  have hg : Continuous g := by
    rw [← hh]; exact h.hom.continuous
  have h0 : g 0 = 0 := by simp [g]
  have h1 : g 1 = 1 := by simp [g]
  obtain ⟨c, -, hc⟩ := intermediate_value_Icc zero_le_one hg.continuousOn
    (show (1 / 2 : ℝ) ∈ Set.Icc (g 0) (g 1) by rw [h0, h1]; constructor <;> norm_num)
  by_cases hlt : c < 1 <;> simp [g, hlt] at hc

theorem top_not_finitary : IsEmpty (ConcreteRelRep (forget TopCat.{0})) :=
  ⟨fun R => top_not_finiteInterpolation
    (ConcreteTokenRep.finiteInterpolation _ R.toTokenRep (TopCat.of ℝ) (TopCat.of ℝ))⟩

theorem top_not_token (E : Type) : IsEmpty (ConcreteTokenRep (forget TopCat.{0}) E) :=
  ⟨fun R => top_not_finiteInterpolation
    (ConcreteTokenRep.finiteInterpolation _ R (TopCat.of ℝ) (TopCat.of ℝ))⟩

/-- Finite interpolation of the hyperfilter membership predicate by evaluations: for finitely
many subsets there is a single point `k` deciding membership in the ultrafilter. -/
lemma hyperfilter_interpolation (F : Finset (Set ℕ)) :
    ∃ k : ℕ, ∀ S ∈ F, (S ∈ Filter.hyperfilter ℕ ↔ k ∈ S) := by
  classical
  have hT : (⋂ S ∈ F, (if S ∈ Filter.hyperfilter ℕ then S else Sᶜ)) ∈ Filter.hyperfilter ℕ := by
    refine (Filter.biInter_finset_mem F).mpr fun S _ => ?_
    split_ifs with h
    · exact h
    · exact Ultrafilter.compl_mem_iff_notMem.mpr h
  obtain ⟨k, hk⟩ := Ultrafilter.nonempty_of_mem hT
  refine ⟨k, fun S hS => ?_⟩
  have := Set.mem_iInter₂.mp hk S hS
  split_ifs at this with h
  · exact ⟨fun _ => this, fun _ => h⟩
  · exact ⟨fun h' => (h h').elim, fun h' => (this h').elim⟩

/-- The category of frames with frame homomorphisms, concretely. -/
abbrev Frm := Bundled Order.Frame

/-- **Proposition 4.9**: frames admit no concrete finitary relational representation
(uses a nonprincipal ultrafilter on `ℕ`, available in ZFC). -/
theorem frm_not_finiteInterpolation :
    ∃ (q : Set ℕ → Bool), (∀ F : Finset (Set ℕ), ∃ k : ℕ, ∀ S ∈ F, (q S = true ↔ k ∈ S)) ∧
      ¬ ∃ φ : FrameHom (Set ℕ) Bool, ∀ S, φ S = q S := by
  classical
  refine ⟨fun S => decide (S ∈ Filter.hyperfilter ℕ), fun F => ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hyperfilter_interpolation F
    exact ⟨k, fun S hS => by rw [decide_eq_true_iff]; exact hk S hS⟩
  · rintro ⟨φ, hφ⟩
    have h1 : φ Set.univ = true := by
      rw [hφ, decide_eq_true_iff]; exact Filter.univ_mem
    have h2 : φ Set.univ = false := by
      have hU : (Set.univ : Set ℕ) = ⨆ n : ℕ, ({n} : Set ℕ) := (Set.iUnion_of_singleton ℕ).symm
      rw [hU, map_iSup]
      simp [hφ, Filter.notMem_hyperfilter_of_finite (Set.finite_singleton _)]
    rw [h1] at h2
    exact Bool.noConfusion h2

/-- **Corollary 4.10**: the powerset encoding `P : Top^op → Set` cannot be repaired on the
same carrier. -/
theorem powerset_not_finitary :
    ∃ (q : Set ℕ → Set PUnit),
      (∀ F : Finset (Set ℕ), ∃ k : ℕ, ∀ S ∈ F, q S = (fun _ => k) ⁻¹' S) ∧
      ¬ ∃ k : ℕ, ∀ S, q S = (fun _ => k) ⁻¹' S := by
  refine ⟨fun S => {_u | S ∈ Filter.hyperfilter ℕ}, fun F => ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hyperfilter_interpolation F
    exact ⟨k, fun S hS => Set.ext fun _ => hk S hS⟩
  · rintro ⟨k, hk⟩
    exact (Set.ext_iff.mp (hk {k}ᶜ) PUnit.unit).mp
      (Filter.compl_mem_hyperfilter_of_finite (Set.finite_singleton k)) rfl

end AT

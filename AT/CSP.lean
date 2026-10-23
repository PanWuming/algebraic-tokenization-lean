import AT.Regular.Defs
import AT.Signature
import AT.Relabel

/-!
# Higher-arity preservation and constraint problems (paper §8)

* `AT.Pol n T = Hom(T^{⊗n}, T)` (positive `n`); **Proposition 8.1** (`AT.pol_iff_polymorphism`,
  `AT.pol_proj`, `AT.pol_comp`): the polymorphism clone.
* Naming forces idempotence (`AT.pol_named_idempotent`); pp-definable relations leave the
  clone unchanged (`AT.pol_pp_invariant`).
* The finite-template problem: `Hom(Rep A, Rep B) ≠ ∅ ↔ CSP(B)` (`AT.csp_iff_hom`);
  the regular-target problem is NP for fixed regular target — only its decidability and the
  3-colouring reduction are formalized (`AT.threeColouring_iff_hom`).
* **Example 8.2** (`AT.booleanAlgebra_hom_two_iff`): nontrivial finite Boolean algebras map to `2`.

The complexity-class assertions (NP-completeness, Bulatov–Zhuk) are not formalized.
-/

universe u v

namespace AT

open CategoryTheory

variable {E : Type v}

/-- The `n`-fold product `T^{⊗n}` with carrier `Fin n → A` (nonempty finite product). -/
def TokenClass.pow (T : TokenClass.{u} E) (n : ℕ) : TokenClass.{u} E where
  carrier := Fin n → T.carrier
  heap := {w | ∀ i : Fin n, wordMap (fun a => a i) w ∈ T.heap}

/-- `Pol_n(T) = Hom(T^{⊗n}, T)`, for `n ≥ 1`. -/
def Pol (T : TokenClass.{u} E) (n : ℕ) : Set ((Fin n → T.carrier) → T.carrier) :=
  TokenClass.admissible (T.pow n) T

/-- A function `p : B^n → B` is an `n`-ary polymorphism of a relational structure. -/
def IsPolymorphism {Sg : RelSig.{v}} (X : RelStr.{u} Sg) {n : ℕ} (p : (Fin n → X.carrier) → X.carrier) : Prop :=
  ∀ (R : Sg.symbols) (rows : Fin n → Fin (Sg.arity R) → X.carrier),
    (∀ i, rows i ∈ X.rel R) → (fun j => p fun i => rows i j) ∈ X.rel R

lemma mem_relRep_heap_iff {Sg : RelSig.{v}} (X : RelStr.{u} Sg) (w : Word X.carrier Sg.toAlgSig.core) :
    w ∈ ((relRep Sg).obj X).heap ↔
      ∃ (R : Sg.symbols) (a : Fin (Sg.arity R) → X.carrier), a ∈ X.rel R ∧
        w = Sum.inr (Sum.inl R) :: (List.ofFn a).map Sum.inl := by
  constructor
  · rintro (⟨R, a, ha, rfl⟩ | ⟨ω, -, -⟩)
    · exact ⟨R, a, ha, rfl⟩
    · exact ω.elim
  · rintro ⟨R, a, ha, rfl⟩
    exact Or.inl ⟨R, a, ha, rfl⟩

/-- **Proposition 8.1**: the underlying functions of `Pol_n(Rep B)` are precisely the `n`-ary
polymorphisms of `B`. -/
theorem pol_iff_polymorphism {Sg : RelSig.{v}} (X : RelStr.{u} Sg) (n : ℕ) (hn : 0 < n)
    (p : (Fin n → X.carrier) → X.carrier) :
    p ∈ Pol ((relRep Sg).obj X) n ↔ IsPolymorphism X p := by
  constructor
  · intro hp R rows hrows
    have hw : (Sum.inr (Sum.inl R) :: (List.ofFn fun j i => rows i j).map Sum.inl :
        Word (Fin n → X.carrier) Sg.toAlgSig.core) ∈ (((relRep Sg).obj X).pow n).heap := by
      intro i
      show wordMap (fun a => a i) (Sum.inr (Sum.inl R) :: (List.ofFn fun j i => rows i j).map Sum.inl)
        ∈ X.toStr.heap
      erw [wordMap_inr_cons_map_inl]
      exact (X.toStr.relRecord_mem_heap_iff R _).mpr (hrows i)
    have := hp _ hw
    change wordMap p (Sum.inr (Sum.inl R) :: (List.ofFn fun j i => rows i j).map Sum.inl)
      ∈ X.toStr.heap at this
    erw [wordMap_inr_cons_map_inl] at this
    exact (X.toStr.relRecord_mem_heap_iff R _).mp this
  · intro hpoly w hw
    change ∀ i, wordMap (fun a => a i) w ∈ X.toStr.heap at hw
    rcases hw ⟨0, hn⟩ with ⟨R, a, -, h0⟩ | ⟨ω, -, -⟩
    swap
    · exact ω.elim
    obtain ⟨a', rfl, -⟩ := exists_of_wordMap_eq_cons _ w _ _ h0
    have hrows : ∀ i, (fun j => a' j i) ∈ X.rel R := by
      intro i
      have := hw i
      erw [wordMap_inr_cons_map_inl] at this
      exact (X.toStr.relRecord_mem_heap_iff R _).mp this
    show wordMap p _ ∈ X.toStr.heap
    erw [wordMap_inr_cons_map_inl]
    exact (X.toStr.relRecord_mem_heap_iff R _).mpr (hpoly R (fun i j => a' j i) hrows)

/-- Projections are polymorphisms. -/
theorem pol_proj (T : TokenClass.{u} E) (n : ℕ) (i : Fin n) : (fun a => a i) ∈ Pol T n :=
  fun _ hw => hw i

/-- Closure under substitution: `p ∘ ⟨q₁,…,q_n⟩`. -/
theorem pol_comp (T : TokenClass.{u} E) {n m : ℕ} (p : (Fin n → T.carrier) → T.carrier)
    (qs : Fin n → (Fin m → T.carrier) → T.carrier) (hp : p ∈ Pol T n) (hq : ∀ i, qs i ∈ Pol T m) :
    (fun a => p fun i => qs i a) ∈ Pol T m := by
  intro w hw
  have hw' : wordMap (fun a i => qs i a) w ∈ (T.pow n).heap := by
    intro i
    have e : wordMap (fun a => a i) (wordMap (fun a i => qs i a) w) = wordMap (qs i) w :=
      (congrFun (wordMap_comp (E := E) (fun a i => qs i a) (fun a => a i)) w).symm
    exact Eq.mpr (congrArg (· ∈ T.heap) e) (hq i w hw)
  have := hp _ hw'
  have e : wordMap p (wordMap (fun a i => qs i a) w) = wordMap (fun a => p fun i => qs i a) w :=
    (congrFun (wordMap_comp (E := E) (fun a i => qs i a) p) w).symm
  exact Eq.mp (congrArg (· ∈ T.heap) e) this

/-- Naming `d ∈ D` by singleton records imposes `p(d,…,d) = d`. -/
theorem pol_named_idempotent (T : TokenClass.{u} E) (D : Set T.carrier) (n : ℕ)
    (p : (Fin n → T.carrier) → T.carrier)
    (hp : p ∈ Pol (nameValues (T := T) (S := ↥D) Subtype.val) n) :
    (∀ d ∈ D, p (fun _ => d) = d) ∧ p ∈ Pol T n := by
  have hrec : ∀ {A : Type u} (u : Word A E) (s : ↥D),
      Sum.inr (Sum.inr s) ∉ relabelWord Sum.inl u := by
    intro A u s h
    simp only [relabelWord, List.mem_map] at h
    obtain ⟨x, -, hx⟩ := h
    rcases x with a | e <;> simp at hx
  constructor
  · intro d hd
    have hw : ([Sum.inr (Sum.inr ⟨d, hd⟩), Sum.inl fun _ => d] :
        Word (Fin n → T.carrier) (E ⊕ ↥D)) ∈ ((nameValues (T := T) Subtype.val).pow n).heap :=
      fun _ => Or.inr ⟨⟨d, hd⟩, rfl⟩
    rcases hp _ hw with ⟨v, -, hv⟩ | ⟨s, hs⟩
    · exact absurd (by rw [hv]; exact List.mem_cons_self ..) (hrec v ⟨d, hd⟩)
    · have hs' : ([Sum.inr (Sum.inr ⟨d, hd⟩), Sum.inl (p fun _ => d)] : Word T.carrier (E ⊕ ↥D)) =
          [Sum.inr (Sum.inr s), Sum.inl s.val] := hs
      obtain ⟨h1, h2⟩ := List.cons.inj hs'
      obtain ⟨h3, -⟩ := List.cons.inj h2
      rw [Sum.inl.inj h3, ← Sum.inr.inj (Sum.inr.inj h1)]
  · intro w hw
    have hw' : relabelWord (E' := E ⊕ ↥D) Sum.inl w ∈
        ((nameValues (T := T) (S := ↥D) Subtype.val).pow n).heap := by
      intro i
      have e := relabelWord_wordMap (E' := E ⊕ ↥D) Sum.inl (fun a : Fin n → T.carrier => a i) w
      exact Eq.mpr (congrArg (· ∈ (nameValues (T := T) (S := ↥D) Subtype.val).heap) e.symm)
        (Or.inl ⟨_, hw i, rfl⟩)
    have := hp _ hw'
    have e := relabelWord_wordMap (E' := E ⊕ ↥D) Sum.inl p w
    have this' : relabelWord (E' := E ⊕ ↥D) Sum.inl (wordMap p w) ∈
        (nameValues (T := T) (S := ↥D) Subtype.val).heap :=
      Eq.mp (congrArg (· ∈ (nameValues (T := T) (S := ↥D) Subtype.val).heap) e.symm) this
    rcases this' with ⟨v, hv, hveq⟩ | ⟨s, hs⟩
    · exact (relabelWord_injective Sum.inl_injective hveq) ▸ hv
    · exact absurd (by rw [hs]; simp) (hrec (wordMap p w) s)

/-- A primitive-positive definition: an existentially quantified conjunction of atoms. We model
its result directly: a relation `R'` such that `a ∈ R' ↔ ∃ witnesses, conjuncts hold`. -/
structure PPDef {Sg : RelSig.{v}} (X : RelStr.{u} Sg) (m : ℕ) where
  witnesses : ℕ
  atoms : List ((R : Sg.symbols) × (Fin (Sg.arity R) → Fin (m + witnesses)))
  eqs : List (Fin (m + witnesses) × Fin (m + witnesses))

def PPDef.rel {Sg : RelSig.{v}} {X : RelStr.{u} Sg} {m : ℕ} (φ : PPDef X m) : Set (Fin m → X.carrier) :=
  {a | ∃ b : Fin φ.witnesses → X.carrier, let v := Fin.append a b
    (∀ t ∈ φ.atoms, (fun j => v (t.2 j)) ∈ X.rel t.1) ∧ ∀ e ∈ φ.eqs, v e.1 = v e.2}

/-- pp-definable relations are preserved by every polymorphism. -/
theorem pol_pp_invariant {Sg : RelSig.{v}} (X : RelStr.{u} Sg) {m n : ℕ} (φ : PPDef X m)
    (p : (Fin n → X.carrier) → X.carrier) (hp : IsPolymorphism X p)
    (rows : Fin n → Fin m → X.carrier) (h : ∀ i, rows i ∈ φ.rel) :
    (fun j => p fun i => rows i j) ∈ φ.rel := by
  dsimp only [PPDef.rel, Set.mem_ofPred_eq] at h ⊢
  choose b hatoms heqs using h
  refine ⟨fun k => p fun i => b i k, ?_, ?_⟩
  · intro t ht
    rw [show (fun j => Fin.append (fun j => p fun i => rows i j) (fun k => p fun i => b i k) (t.2 j)) =
        fun j => p fun i => Fin.append (rows i) (b i) (t.2 j) from
        funext fun j => Fin.addCases (fun j => by simp [Fin.append_left])
          (fun j => by simp [Fin.append_right]) (t.2 j)]
    exact hp t.1 (fun i j => Fin.append (rows i) (b i) (t.2 j)) (fun i => hatoms i t ht)
  · intro e he
    have hv : ∀ k, Fin.append (fun j => p fun i => rows i j) (fun k => p fun i => b i k) k =
        p fun i => Fin.append (rows i) (b i) k := fun k =>
      Fin.addCases (fun j => by simp [Fin.append_left]) (fun j => by simp [Fin.append_right]) k
    rw [hv, hv]
    exact congrArg p (funext fun i => heqs i e he)

/-! ### The finite-template decision problem (§8.2) -/

/-- `CSP(B)`: existence of a relational homomorphism `A → B`. -/
def CSP {Sg : RelSig.{v}} (B : RelStr.{u} Sg) (A : RelStr.{u} Sg) : Prop := Nonempty (A ⟶ B)

/-- Full faithfulness identifies the Token-map existence problem (8.2) with `CSP(B)`. -/
theorem csp_iff_hom {Sg : RelSig.{v}} (B A : RelStr.{u} Sg) :
    CSP B A ↔ Nonempty ((relRep Sg).obj A ⟶ (relRep Sg).obj B) := by
  constructor
  · rintro ⟨f⟩
    exact ⟨(relRep Sg).map f⟩
  · rintro ⟨g⟩
    obtain ⟨f, -⟩ := (Rep Sg.toAlgSig).map_surjective (X := A.toStr) (Y := B.toStr) g
    exact ⟨⟨f.toFun, f.preserves_rel⟩⟩

/-- For finite template and instance, `CSP(B)` is decidable. -/
def csp_decidable {Sg : RelSig.{v}} (B A : RelStr.{u} Sg) [Fintype A.carrier] [Fintype B.carrier]
    [DecidableEq A.carrier] [DecidableEq B.carrier] [Fintype Sg.symbols]
    [∀ R, DecidablePred (· ∈ A.rel R)] [∀ R, DecidablePred (· ∈ B.rel R)] : Decidable (CSP B A) :=
  decidable_of_iff (∃ f : A.carrier → B.carrier, ∀ (R : Sg.symbols) (a : Fin (Sg.arity R) → A.carrier),
      a ∈ A.rel R → f ∘ a ∈ B.rel R)
    ⟨fun ⟨f, hf⟩ => ⟨⟨f, hf⟩⟩, fun ⟨f⟩ => ⟨f.toFun, f.preserves⟩⟩

/-- The fixed regular target `K = {(e,i,j) : i ≠ j}` on `B = {1,2,3}`. -/
def threeColourTarget : TokenClass.{0} Unit :=
  ⟨Fin 3, {w | ∃ i j : Fin 3, i ≠ j ∧ w = [Sum.inr (), Sum.inl i, Sum.inl j]}⟩

/-- Finite languages are regular (Myhill–Nerode: all left quotients are sets of suffixes). -/
private theorem isRegular_of_finite_aux {α : Type*} {L : Language α}
    (h : (L : Set (List α)).Finite) : L.IsRegular := by
  rw [Language.isRegular_iff_finite_range_leftQuotient]
  let S : Set (List α) := {y | ∃ x, x ++ y ∈ L}
  have hS : S.Finite := by
    refine Set.Finite.subset (h.biUnion fun w _ => (w.tails.finite_toSet)) ?_
    rintro y ⟨x, hx⟩
    exact Set.mem_biUnion hx ((List.mem_tails _ _).mpr ⟨x, rfl⟩)
  refine Set.Finite.subset (hS.finite_subsets) ?_
  rintro _ ⟨x, rfl⟩
  intro y hy
  exact ⟨x, hy⟩

theorem threeColourTarget_regular : threeColourTarget.IsRegularHeap := by
  refine isRegular_of_finite_aux (Set.Finite.subset
    (Set.finite_range fun p : Fin 3 × Fin 3 => [Sum.inr (), Sum.inl p.1, Sum.inl p.2]) ?_)
  rintro _ ⟨i, j, -, rfl⟩
  exact ⟨(i, j), rfl⟩

/-- The edge heap of a graph, in both orientations. -/
def graphHeap {V : Type} (G : SimpleGraph V) : TokenClass.{0} Unit :=
  ⟨V, {w | ∃ u v, G.Adj u v ∧ w = [Sum.inr (), Sum.inl u, Sum.inl v]}⟩

/-- A preserving map is precisely a proper 3-colouring. -/
theorem threeColouring_iff_hom {V : Type} (G : SimpleGraph V) :
    G.Colorable 3 ↔ Nonempty (graphHeap G ⟶ threeColourTarget) := by
  constructor
  · rintro ⟨c⟩
    refine ⟨⟨c, ?_⟩⟩
    rintro w ⟨u, v, huv, rfl⟩
    exact ⟨c u, c v, c.valid huv, rfl⟩
  · rintro ⟨f⟩
    refine ⟨SimpleGraph.Coloring.mk f.toFun fun {u v} huv => ?_⟩
    obtain ⟨i, j, hij, h⟩ := f.preserves _ ⟨u, v, huv, rfl⟩
    simp [wordMap] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hij

theorem graphHeap_finite_regular {V : Type} [Finite V] (G : SimpleGraph V) :
    (graphHeap G).heap.Finite ∧ (graphHeap G).IsRegularHeap := by
  have hfin : (graphHeap G).heap.Finite := by
    refine Set.Finite.subset
      (Set.finite_range fun p : V × V => [Sum.inr (), Sum.inl p.1, Sum.inl p.2]) ?_
    rintro _ ⟨u, v, -, rfl⟩
    exact ⟨(u, v), rfl⟩
  exact ⟨hfin, isRegular_of_finite_aux hfin⟩

/-! ### Example 8.2: Boolean algebras versus Boolean constraints -/

/-- **Example 8.2**: a finite Boolean algebra has a Boolean-algebra homomorphism to `Bool`
exactly when it is nontrivial. The homomorphism is `h_a(x) = 1 ↔ a ≤ x` for an atom `a`. -/
theorem booleanAlgebra_hom_two_iff (A : Type u) [BooleanAlgebra A] [Finite A] :
    Nonempty (BoundedLatticeHom A Bool) ↔ Nontrivial A := by
  constructor
  · rintro ⟨f⟩
    refine ⟨⟨⊤, ⊥, fun h => ?_⟩⟩
    have := congrArg f h
    rw [map_top, map_bot] at this
    exact Bool.noConfusion this
  · intro hA
    obtain ⟨a, ha, -⟩ := (eq_bot_or_exists_atom_le (⊤ : A)).resolve_left top_ne_bot
    have hsup : ∀ x y : A, a ≤ x ⊔ y ↔ a ≤ x ∨ a ≤ y := by
      intro x y
      refine ⟨fun h => ?_, fun h => h.elim (le_trans · le_sup_left) (le_trans · le_sup_right)⟩
      have hx := ha.le_iff.mp (inf_le_left : a ⊓ x ≤ a)
      have hy := ha.le_iff.mp (inf_le_left : a ⊓ y ≤ a)
      rcases hx with hx | hx
      · rcases hy with hy | hy
        · exfalso
          apply ha.1
          calc a = a ⊓ (x ⊔ y) := (inf_eq_left.mpr h).symm
            _ = (a ⊓ x) ⊔ (a ⊓ y) := inf_sup_left _ _ _
            _ = ⊥ := by rw [hx, hy, bot_sup_eq]
        · exact Or.inr (inf_eq_left.mp hy)
      · exact Or.inl (inf_eq_left.mp hx)
    classical
    refine ⟨⟨⟨⟨fun x => decide (a ≤ x), ?_⟩, ?_⟩, ?_, ?_⟩⟩
    · intro x y
      by_cases hx : a ≤ x <;> by_cases hy : a ≤ y <;> simp [hx, hy, hsup]
    · intro x y
      by_cases hx : a ≤ x <;> by_cases hy : a ≤ y <;> simp [hx, hy, le_inf_iff]
    · simp
    · simp [ha.1]

end AT

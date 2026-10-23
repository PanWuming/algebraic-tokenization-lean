import AT.Relabel

/-!
# Parameters as data and the control of symmetry (paper §7)

* `AT.Sorted` — structures on a tagged carrier `D ⊔ P` with sort records (§7.1);
  **Proposition 7.1** (`AT.Sorted.restrictAut`, exact sequence).
* **Proposition 7.2** (`AT.Sorted.nameValues_hom_iff`): named parameters = pointwise stabilizer.
* `AT.ScalarRep k V = Q_k(V)` (§7.3); **Proposition 7.3** (`AT.scalarRep_hom_iff`): semilinear maps.
* **Lemma 7.4** (`AT.real_ringHom_eq_id`), **Theorem 7.5** (`AT.complexRep_hom_iff`),
  **Proposition 7.6** (`AT.complex_countable_names_insufficient`),
  **Proposition 7.7** (`AT.finiteField_named_generator_rigid`), **Remark 7.8**.
-/

universe u v

namespace AT

open CategoryTheory

/-- A relabelled word never starts with a label outside the image of `α`. -/
theorem relabelWord_ne_cons_inr {A : Type u} {E : Type v} {E' : Type*} (α : E → E') (w : Word A E)
    (e' : E') (he : ∀ e, α e ≠ e') (v : Word A E') : relabelWord α w ≠ Sum.inr e' :: v := by
  cases w with
  | nil => simp [relabelWord]
  | cons a w =>
    rcases a with a | e
    · simp [relabelWord]
    · simp [relabelWord, he e]

theorem wordMap_injective {A B : Type u} {E : Type v} {f : A → B} (hf : Function.Injective f) :
    Function.Injective (wordMap (E := E) f) :=
  List.map_injective_iff.mpr (Sum.map_injective.mpr ⟨hf, Function.injective_id⟩)

/-! ### Sorted parameter carriers (§7.1) -/

/-- Core labels for a sorted encoding: the two sort predicates plus the labels of `E`. -/
inductive SortLabel (E : Type v)
  | dataSort | paramSort | lab : E → SortLabel E

/-- A Token class on `D ⊔ P` with unary sort records and a fixed parameter heap `H_P` on `P`,
plus further records connecting data and parameters. -/
structure Sorted (E : Type v) (P : Type u) (HP : Set (Word P E)) where
  data : Type u
  connect : Set (Word (data ⊕ P) E)
  /-- Connecting records genuinely connect data to parameters: each mentions a datum. (The
  records living purely on the parameter sort are exactly those of `HP`.) -/
  connect_data : ∀ w ∈ connect, ∃ d : data, Sum.inl (Sum.inl d) ∈ w

namespace Sorted

variable {E : Type v} {P : Type u} {HP : Set (Word P E)}

/-- The Token class of a sorted structure. -/
def toTokenClass (M : Sorted.{u,v} E P HP) : TokenClass.{u} (SortLabel E) where
  carrier := M.data ⊕ P
  heap := {w | ∃ d, w = [Sum.inr .dataSort, Sum.inl (Sum.inl d)]} ∪
          {w | ∃ p, w = [Sum.inr .paramSort, Sum.inl (Sum.inr p)]} ∪
          relabelWord SortLabel.lab '' (wordMap Sum.inr '' HP) ∪
          relabelWord SortLabel.lab '' M.connect

theorem dataSort_mem_iff (M : Sorted.{u,v} E P HP) (x : M.data ⊕ P) :
    [Sum.inr .dataSort, Sum.inl x] ∈ M.toTokenClass.heap ↔ ∃ d, x = Sum.inl d := by
  simp only [toTokenClass]
  constructor
  · rintro (((⟨d, hd⟩ | ⟨p, hp⟩) | ⟨w, -, hw⟩) | ⟨w, -, hw⟩)
    · simp only [List.cons.injEq, Sum.inl.injEq, and_true, true_and] at hd; exact ⟨d, hd⟩
    · simp at hp
    · exact absurd hw (relabelWord_ne_cons_inr _ _ _ (fun e => by simp) _)
    · exact absurd hw (relabelWord_ne_cons_inr _ _ _ (fun e => by simp) _)
  · rintro ⟨d, rfl⟩; exact Or.inl (Or.inl (Or.inl ⟨d, rfl⟩))

theorem paramSort_mem_iff (M : Sorted.{u,v} E P HP) (x : M.data ⊕ P) :
    [Sum.inr .paramSort, Sum.inl x] ∈ M.toTokenClass.heap ↔ ∃ p, x = Sum.inr p := by
  simp only [toTokenClass]
  constructor
  · rintro (((⟨d, hd⟩ | ⟨p, hp⟩) | ⟨w, -, hw⟩) | ⟨w, -, hw⟩)
    · simp at hd
    · simp only [List.cons.injEq, Sum.inl.injEq, and_true, true_and] at hp; exact ⟨p, hp⟩
    · exact absurd hw (relabelWord_ne_cons_inr _ _ _ (fun e => by simp) _)
    · exact absurd hw (relabelWord_ne_cons_inr _ _ _ (fun e => by simp) _)
  · rintro ⟨p, rfl⟩; exact Or.inl (Or.inl (Or.inr ⟨p, rfl⟩))

variable {M N : Sorted.{u,v} E P HP}

theorem toFun_inl_isLeft (h : M.toTokenClass ⟶ N.toTokenClass) (d : M.data) :
    (h.toFun (Sum.inl d)).isLeft = true := by
  have : [Sum.inr .dataSort, Sum.inl (h.toFun (Sum.inl d))] ∈ N.toTokenClass.heap :=
    h.preserves _ ((dataSort_mem_iff M (Sum.inl d)).mpr ⟨d, rfl⟩)
  obtain ⟨d', hd'⟩ := (dataSort_mem_iff N _).mp this
  simp [hd']

theorem toFun_inr_isRight (h : M.toTokenClass ⟶ N.toTokenClass) (p : P) :
    (h.toFun (Sum.inr p)).isRight = true := by
  have : [Sum.inr .paramSort, Sum.inl (h.toFun (Sum.inr p))] ∈ N.toTokenClass.heap :=
    h.preserves _ ((paramSort_mem_iff M (Sum.inr p)).mpr ⟨p, rfl⟩)
  obtain ⟨p', hp'⟩ := (paramSort_mem_iff N _).mp this
  simp [hp']

/-- The data component `f` of a Token map `h = f ⊔ σ`. -/
def dataComp (h : M.toTokenClass ⟶ N.toTokenClass) (d : M.data) : N.data :=
  (h.toFun (Sum.inl d)).getLeft (toFun_inl_isLeft h d)

/-- The parameter component `σ` of a Token map `h = f ⊔ σ`. -/
def paramComp (h : M.toTokenClass ⟶ N.toTokenClass) (p : P) : P :=
  (h.toFun (Sum.inr p)).getRight (toFun_inr_isRight h p)

@[simp] theorem toFun_inl (h : M.toTokenClass ⟶ N.toTokenClass) (d : M.data) :
    h.toFun (Sum.inl d) = Sum.inl (dataComp h d) :=
  (Sum.inl_getLeft _ _).symm

@[simp] theorem toFun_inr (h : M.toTokenClass ⟶ N.toTokenClass) (p : P) :
    h.toFun (Sum.inr p) = Sum.inr (paramComp h p) :=
  (Sum.inr_getRight _ _).symm

theorem toFun_eq (h : M.toTokenClass ⟶ N.toTokenClass) :
    h.toFun = Sum.map (dataComp h) (paramComp h) := by
  funext x
  cases x with
  | inl d => exact toFun_inl h d
  | inr p => exact toFun_inr h p

/-- Sort preservation splits a Token map as `f ⊔ σ`. -/
theorem hom_split (M N : Sorted.{u,v} E P HP) (h : M.toTokenClass ⟶ N.toTokenClass) :
    ∃ (f : M.data → N.data) (σ : P → P), h.toFun = Sum.map f σ :=
  ⟨_, _, toFun_eq h⟩

theorem paramComp_eq (h : M.toTokenClass ⟶ N.toTokenClass) (f : M.data → N.data) (σ : P → P)
    (hσ : h.toFun = Sum.map f σ) : paramComp h = σ := by
  funext p
  have := congrFun hσ (Sum.inr p)
  rw [toFun_inr] at this
  exact Sum.inr_injective this

theorem paramComp_id (M : Sorted.{u,v} E P HP) : paramComp (𝟙 M.toTokenClass) = id := by
  funext p; apply Sum.inr_injective; rw [← toFun_inr]; rfl

theorem paramComp_comp {L : Sorted.{u,v} E P HP} (g : L.toTokenClass ⟶ M.toTokenClass)
    (h : M.toTokenClass ⟶ N.toTokenClass) :
    paramComp (g ≫ h) = paramComp h ∘ paramComp g := by
  funext p; apply Sum.inr_injective
  rw [← toFun_inr]
  change h.toFun (g.toFun (Sum.inr p)) = _
  rw [toFun_inr, toFun_inr]
  rfl

theorem paramComp_isHom (h : M.toTokenClass ⟶ N.toTokenClass) :
    TokenClass.IsHom (⟨P, HP⟩ : TokenClass.{u} E) ⟨P, HP⟩ (paramComp h) := by
  intro (w : Word P E) hw
  have hmem : relabelWord SortLabel.lab (wordMap (Sum.inr : P → M.data ⊕ P) w) ∈
      M.toTokenClass.heap :=
    Or.inl (Or.inr ⟨_, ⟨w, hw, rfl⟩, rfl⟩)
  have himg : wordMap h.toFun (relabelWord SortLabel.lab (wordMap (Sum.inr : P → M.data ⊕ P) w)) ∈
      N.toTokenClass.heap := h.preserves _ hmem
  have key : wordMap h.toFun (relabelWord SortLabel.lab (wordMap (Sum.inr : P → M.data ⊕ P) w)) =
      relabelWord SortLabel.lab (wordMap (Sum.inr : P → N.data ⊕ P) (wordMap (paramComp h) w)) := by
    simp only [relabelWord, wordMap, List.map_map]
    congr 1
    funext x
    rcases x with x | e
    · exact congrArg Sum.inl (toFun_inr h x)
    · rfl
  rw [key] at himg
  rcases himg with ((⟨d, hd⟩ | ⟨p, hp⟩) | ⟨u, ⟨u', hu', rfl⟩, hu⟩) | ⟨c, hc, hcw⟩
  · exact absurd hd (relabelWord_ne_cons_inr _ _ _ (fun e => by simp) _)
  · exact absurd hp (relabelWord_ne_cons_inr _ _ _ (fun e => by simp) _)
  · have := wordMap_injective Sum.inr_injective
      (relabelWord_injective (fun _ _ h => SortLabel.lab.inj h) hu)
    rw [← this]; exact hu'
  · exfalso
    have hc' := relabelWord_injective (fun _ _ h => SortLabel.lab.inj h) hcw
    obtain ⟨d, hd⟩ := N.connect_data c hc
    rw [hc'] at hd
    simp only [wordMap, List.mem_map] at hd
    obtain ⟨x, -, hx⟩ := hd
    rcases x with x | x <;> simp at hx

/-- The parameter component lies in `End(P)`. -/
theorem hom_param_component (M N : Sorted.{u,v} E P HP) (h : M.toTokenClass ⟶ N.toTokenClass)
    (f : M.data → N.data) (σ : P → P) (hσ : h.toFun = Sum.map f σ) :
    TokenClass.IsHom (⟨P, HP⟩ : TokenClass.{u} E) ⟨P, HP⟩ σ := by
  rw [← paramComp_eq h f σ hσ]; exact paramComp_isHom h

/-- `Hom_P(M,N)`: homomorphisms whose parameter component is `id_P`. -/
def HomP (M N : Sorted.{u,v} E P HP) : Set (M.toTokenClass ⟶ N.toTokenClass) :=
  {h | ∃ f : M.data → N.data, h.toFun = Sum.map f id}

/-- Restriction of a Token map to the parameter sort. -/
def restrictHom (h : M.toTokenClass ⟶ N.toTokenClass) :
    (⟨P, HP⟩ : TokenClass.{u} E) ⟶ ⟨P, HP⟩ :=
  ⟨paramComp h, paramComp_isHom h⟩

/-- **Proposition 7.1**: restriction `ρ_M : Aut(M) → Aut(P)` is a group homomorphism. -/
def restrictAut (M : Sorted.{u,v} E P HP) :
    Aut M.toTokenClass →* Aut (⟨P, HP⟩ : TokenClass.{u} E) where
  toFun g := Aut.of
    { hom := restrictHom g.asIso.hom
      inv := restrictHom g.asIso.inv
      hom_inv_id := TokenClass.Hom.ext (by
        change paramComp g.asIso.inv ∘ paramComp g.asIso.hom = id
        rw [← paramComp_comp, g.asIso.hom_inv_id, paramComp_id])
      inv_hom_id := TokenClass.Hom.ext (by
        change paramComp g.asIso.hom ∘ paramComp g.asIso.inv = id
        rw [← paramComp_comp, g.asIso.inv_hom_id, paramComp_id]) }
  map_one' := by
    apply Aut.ext; apply Iso.ext; apply TokenClass.Hom.ext
    exact paramComp_id M
  map_mul' x y := by
    apply Aut.ext; apply Iso.ext; apply TokenClass.Hom.ext
    exact paramComp_comp _ _

/-- **Proposition 7.1**: the kernel of `ρ_M` is `Aut_P(M)`. -/
theorem restrictAut_ker (M : Sorted.{u,v} E P HP) (g : M.toTokenClass ≅ M.toTokenClass) :
    Aut.of g ∈ (restrictAut M).ker ↔ g.hom ∈ HomP M M := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg
    refine ⟨dataComp g.hom, ?_⟩
    have : paramComp g.hom = id := congrArg (fun a : Aut (⟨P, HP⟩ : TokenClass.{u} E) =>
      a.asIso.hom.toFun) hg
    rw [toFun_eq g.hom, this]
  · rintro ⟨f, hf⟩
    apply Aut.ext; apply Iso.ext; apply TokenClass.Hom.ext
    exact paramComp_eq g.hom f id hf

/-- **Proposition 7.1**: if `End(P) = {id}` then `Hom_P(M,N) = Hom(M,N)`. -/
theorem homP_eq_hom_of_rigid (hrig : ∀ σ, TokenClass.IsHom (⟨P, HP⟩ : TokenClass.{u} E) ⟨P, HP⟩ σ → σ = id)
    (M N : Sorted.{u,v} E P HP) : HomP M N = Set.univ := by
  ext h
  refine ⟨fun _ => trivial, fun _ => ⟨dataComp h, ?_⟩⟩
  rw [toFun_eq h, hrig _ (paramComp_isHom h)]

/-- Absolute naming `M[K]`: adjoin a fresh symbol `c_p` and the record `(c_p, p)` for `p ∈ K`. -/
abbrev nameParams (M : Sorted.{u,v} E P HP) (K : Set P) : TokenClass.{u} (SortLabel E ⊕ ↥K) :=
  nameValues (T := M.toTokenClass) (S := ↥K) fun p => Sum.inr p.1

/-- **Proposition 7.2** (named parameters): `Hom(M[K],N[K]) = {f ⊔ σ : σ|_K = id}`. -/
theorem nameParams_hom_iff (M N : Sorted.{u,v} E P HP) (K : Set P) (h : M.toTokenClass.carrier → N.toTokenClass.carrier) :
    TokenClass.IsHom (M.nameParams K) (N.nameParams K) h ↔
      TokenClass.IsHom M.toTokenClass N.toTokenClass h ∧ ∀ p ∈ K, h (Sum.inr p) = Sum.inr p := by
  have := nameValues_hom_iff (T₁ := M.toTokenClass) (T₂ := N.toTokenClass) (S := ↥K)
    (fun p => Sum.inr p.1) (fun p => Sum.inr p.1) h
  refine this.trans (and_congr_right fun _ => ⟨fun hf p hp => congrFun hf ⟨p, hp⟩, fun hf => ?_⟩)
  funext p
  exact hf p.1 p.2

end Sorted

/-! ### Scalar parameters and semilinear maps (§7.3) -/

/-- Core labels for `Q_k(V)`: sorts, vector addition, scalar action, vector zero, and the ring
graphs and constants `+_k, ·_k, -_k, 0_k, 1_k`. -/
inductive ScalarLabel
  | sortV | sortK | add | act | zero | addK | mulK | negK | zeroK | oneK
  deriving DecidableEq

/-- All scalar labels. -/
def ScalarLabel.all : List ScalarLabel :=
  [.sortV, .sortK, .add, .act, .zero, .addK, .mulK, .negK, .zeroK, .oneK]

instance : Fintype ScalarLabel :=
  Fintype.ofList ScalarLabel.all (fun x => by cases x <;> simp [ScalarLabel.all])

/-- `Q_k(V)` on `V ⊔ k` (§7.3). Records have length at most four. -/
def ScalarRep (k : Type u) [Field k] (V : Type u) [AddCommGroup V] [Module k V] :
    TokenClass.{u} ScalarLabel where
  carrier := V ⊕ k
  heap :=
    {w | ∃ v : V, w = [Sum.inr .sortV, Sum.inl (Sum.inl v)]} ∪
    {w | ∃ a : k, w = [Sum.inr .sortK, Sum.inl (Sum.inr a)]} ∪
    {w | ∃ v w' : V, w = [Sum.inr .add, Sum.inl (Sum.inl v), Sum.inl (Sum.inl w'), Sum.inl (Sum.inl (v + w'))]} ∪
    {w | ∃ (a : k) (v : V), w = [Sum.inr .act, Sum.inl (Sum.inr a), Sum.inl (Sum.inl v), Sum.inl (Sum.inl (a • v))]} ∪
    {[Sum.inr .zero, Sum.inl (Sum.inl 0)]} ∪
    {w | ∃ a b : k, w = [Sum.inr .addK, Sum.inl (Sum.inr a), Sum.inl (Sum.inr b), Sum.inl (Sum.inr (a + b))]} ∪
    {w | ∃ a b : k, w = [Sum.inr .mulK, Sum.inl (Sum.inr a), Sum.inl (Sum.inr b), Sum.inl (Sum.inr (a * b))]} ∪
    {w | ∃ a : k, w = [Sum.inr .negK, Sum.inl (Sum.inr a), Sum.inl (Sum.inr (-a))]} ∪
    {[Sum.inr .zeroK, Sum.inl (Sum.inr 0)]} ∪
    {[Sum.inr .oneK, Sum.inl (Sum.inr 1)]}

variable {k : Type u} [Field k] {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- A semilinear pair `(σ, f)`: `σ` a unital field endomorphism, `f` additive, `f(av) = σ(a) f(v)`. -/
def IsSemilinearPair (σ : k → k) (f : V → W) : Prop :=
  (∃ σ' : k →+* k, ⇑σ' = σ) ∧ (∃ f' : V →+ W, ⇑f' = f) ∧ ∀ (a : k) (v : V), f (a • v) = σ a • f v

/-- **Proposition 7.3** (the maps admitted by scalar reification): Token maps
`Q_k(V) → Q_k(W)` are exactly the semilinear pairs. -/
theorem scalarRep_hom_iff (h : V ⊕ k → W ⊕ k) :
    TokenClass.IsHom (ScalarRep k V) (ScalarRep k W) h ↔
      ∃ (σ : k → k) (f : V → W), h = Sum.map f σ ∧ IsSemilinearPair σ f := by
  constructor
  · intro hh
    have hV : ∀ v : V, ∃ v', h (Sum.inl v) = Sum.inl v' := fun v => by
      have := hh [Sum.inr .sortV, Sum.inl (Sum.inl v)] (by unfold ScalarRep; simp)
      unfold ScalarRep at this
      simp only [wordMap, List.map_cons, List.map_nil, Sum.map_inl, Sum.map_inr, id] at this
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq] at this
      simpa using this
    have hk : ∀ a : k, ∃ a', h (Sum.inr a) = Sum.inr a' := fun a => by
      have := hh [Sum.inr .sortK, Sum.inl (Sum.inr a)] (by unfold ScalarRep; simp)
      unfold ScalarRep at this
      simp only [wordMap, List.map_cons, List.map_nil, Sum.map_inl, Sum.map_inr, id] at this
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq] at this
      simpa using this
    choose f hf using hV
    choose σ hσ using hk
    have hadd : ∀ v w : V, f (v + w) = f v + f w := fun v w => by
      have := hh [Sum.inr .add, Sum.inl (Sum.inl v), Sum.inl (Sum.inl w), Sum.inl (Sum.inl (v + w))]
        (by unfold ScalarRep; simp)
      unfold ScalarRep at this
      simp only [wordMap, List.map_cons, List.map_nil, Sum.map_inl, Sum.map_inr, id, hf] at this
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq] at this
      simpa using this
    have hzero : f 0 = 0 := by
      have := hh [Sum.inr .zero, Sum.inl (Sum.inl 0)] (by unfold ScalarRep; simp)
      unfold ScalarRep at this
      simp only [wordMap, List.map_cons, List.map_nil, Sum.map_inl, Sum.map_inr, id, hf] at this
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq] at this
      simpa using this
    have hact : ∀ (a : k) (v : V), f (a • v) = σ a • f v := fun a v => by
      have := hh [Sum.inr .act, Sum.inl (Sum.inr a), Sum.inl (Sum.inl v), Sum.inl (Sum.inl (a • v))]
        (by unfold ScalarRep; simp)
      unfold ScalarRep at this
      simp only [wordMap, List.map_cons, List.map_nil, Sum.map_inl, Sum.map_inr, id, hf, hσ] at this
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq] at this
      simpa using this
    have haddK : ∀ a b : k, σ (a + b) = σ a + σ b := fun a b => by
      have := hh [Sum.inr .addK, Sum.inl (Sum.inr a), Sum.inl (Sum.inr b), Sum.inl (Sum.inr (a + b))]
        (by unfold ScalarRep; simp)
      unfold ScalarRep at this
      simp only [wordMap, List.map_cons, List.map_nil, Sum.map_inl, Sum.map_inr, id, hσ] at this
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq] at this
      simpa using this
    have hmulK : ∀ a b : k, σ (a * b) = σ a * σ b := fun a b => by
      have := hh [Sum.inr .mulK, Sum.inl (Sum.inr a), Sum.inl (Sum.inr b), Sum.inl (Sum.inr (a * b))]
        (by unfold ScalarRep; simp)
      unfold ScalarRep at this
      simp only [wordMap, List.map_cons, List.map_nil, Sum.map_inl, Sum.map_inr, id, hσ] at this
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq] at this
      simpa using this
    have hzeroK : σ 0 = 0 := by
      have := hh [Sum.inr .zeroK, Sum.inl (Sum.inr 0)] (by unfold ScalarRep; simp)
      unfold ScalarRep at this
      simp only [wordMap, List.map_cons, List.map_nil, Sum.map_inl, Sum.map_inr, id, hσ] at this
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq] at this
      simpa using this
    have honeK : σ 1 = 1 := by
      have := hh [Sum.inr .oneK, Sum.inl (Sum.inr 1)] (by unfold ScalarRep; simp)
      unfold ScalarRep at this
      simp only [wordMap, List.map_cons, List.map_nil, Sum.map_inl, Sum.map_inr, id, hσ] at this
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq] at this
      simpa using this
    refine ⟨σ, f, ?_, ⟨⟨⟨⟨σ, honeK⟩, hmulK⟩, hzeroK, haddK⟩, rfl⟩, ⟨⟨⟨f, hzero⟩, hadd⟩, rfl⟩, hact⟩
    funext x; rcases x with v | a
    · exact hf v
    · exact hσ a
  · rintro ⟨σ, f, rfl, ⟨σ', rfl⟩, ⟨f', rfl⟩, hact⟩
    intro w hw
    unfold ScalarRep at hw ⊢
    rcases hw with ((((((((⟨v, rfl⟩ | ⟨a, rfl⟩) | ⟨v, w', rfl⟩) | ⟨a, v, rfl⟩) | rfl) | ⟨a, b, rfl⟩) |
      ⟨a, b, rfl⟩) | ⟨a, rfl⟩) | rfl) | rfl
    all_goals simp [wordMap, hact]

/-- The encoding of linear maps by `(id_k, f)`. -/
def ScalarRep.ofLinear (f : V →ₗ[k] W) : ScalarRep k V ⟶ ScalarRep k W :=
  ⟨Sum.map f id, (scalarRep_hom_iff _).mpr
    ⟨id, f, rfl, ⟨RingHom.id k, rfl⟩, ⟨f.toAddMonoidHom, rfl⟩, fun a v => by simp⟩⟩

theorem ScalarRep.ofLinear_injective : Function.Injective (ScalarRep.ofLinear (k := k) (V := V) (W := W)) := by
  intro f g hfg
  ext v
  have := congrFun (congrArg TokenClass.Hom.toFun hfg) (Sum.inl v)
  exact Sum.inl_injective this

/-- **Proposition 7.3** (fullness): on all `k`-vector spaces, the linear encoding is full iff
`End(k) = {id_k}`. -/
theorem scalarRep_full_iff :
    (∀ (V W : Type u) [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
        (h : ScalarRep k V ⟶ ScalarRep k W), ∃ f : V →ₗ[k] W, h = ScalarRep.ofLinear f) ↔
      ∀ σ : k →+* k, σ = RingHom.id k := by
  constructor
  · intro hfull σ
    let h : ScalarRep k PUnit ⟶ ScalarRep k PUnit :=
      ⟨Sum.map (fun _ => PUnit.unit) σ, (scalarRep_hom_iff _).mpr
        ⟨σ, fun _ => PUnit.unit, rfl, ⟨σ, rfl⟩, ⟨0, rfl⟩, fun _ _ => rfl⟩⟩
    obtain ⟨f, hf⟩ := hfull PUnit PUnit h
    ext a
    have := congrFun (congrArg TokenClass.Hom.toFun hf) (Sum.inr a)
    exact Sum.inr_injective this
  · intro hrig V W _ _ _ _ h
    obtain ⟨σ, f, hh, ⟨σ', hσ'⟩, ⟨f', hf'⟩, hact⟩ := (scalarRep_hom_iff h.toFun).mp h.preserves
    have hσ : σ = id := by rw [← hσ', hrig σ']; rfl
    subst hσ
    refine ⟨{ toFun := f
              map_add' := fun v w => by rw [← hf']; exact map_add f' v w
              map_smul' := fun a v => by simpa using hact a v }, ?_⟩
    apply TokenClass.Hom.ext
    exact hh

/-- Every record of `Q_k(V)` has length at most four. -/
theorem scalarRep_record_length (w : Word (V ⊕ k) ScalarLabel) (hw : w ∈ (ScalarRep k V).heap) :
    w.length ≤ 4 := by
  unfold ScalarRep at hw
  rcases hw with ((((((((⟨v, rfl⟩ | ⟨a, rfl⟩) | ⟨v, w', rfl⟩) | ⟨a, v, rfl⟩) | rfl) | ⟨a, b, rfl⟩) |
    ⟨a, b, rfl⟩) | ⟨a, rfl⟩) | rfl) | rfl
  all_goals simp

/-- **Lemma 7.4** (real scalar rigidity): every unital field endomorphism of `ℝ` is the identity. -/
theorem real_ringHom_eq_id (σ : ℝ →+* ℝ) : σ = RingHom.id ℝ := Subsingleton.elim _ _

/-! ### Restoring complex linearity with a finite core (§7.4) -/

/-- Core labels of `Q_ℂ^†(V)`: the scalar labels plus conjugation and a name for `i`. -/
inductive ComplexLabel
  | base : ScalarLabel → ComplexLabel | conj | imagUnit
  deriving DecidableEq

instance : Fintype ComplexLabel :=
  Fintype.ofList (ScalarLabel.all.map .base ++ [.conj, .imagUnit])
    (fun x => by cases x with
      | base b => cases b <;> simp [ScalarLabel.all]
      | _ => simp)

/-- `Q_ℂ^†(V)`: `Q_ℂ(V)` enriched by the graph of conjugation and a constant naming `i`. -/
def ComplexRep (V : Type) [AddCommGroup V] [Module ℂ V] : TokenClass.{0} ComplexLabel where
  carrier := V ⊕ ℂ
  heap := relabelWord ComplexLabel.base '' (ScalarRep ℂ V).heap ∪
    {w | ∃ z : ℂ, w = [Sum.inr .conj, Sum.inl (Sum.inr z), Sum.inl (Sum.inr (starRingEnd ℂ z))]} ∪
    {[Sum.inr .imagUnit, Sum.inl (Sum.inr Complex.I)]}

/-- Key step of Theorem 7.5: a ring endomorphism of `ℂ` commuting with conjugation and fixing
`i` is the identity. -/
theorem complex_ringHom_eq_id_of_conj_of_I (σ : ℂ →+* ℂ)
    (hc : ∀ z, σ (starRingEnd ℂ z) = starRingEnd ℂ (σ z)) (hi : σ Complex.I = Complex.I) :
    σ = RingHom.id ℂ := by
  have him : ∀ a : ℝ, (σ a).im = 0 := fun a => by
    rw [← Complex.conj_eq_iff_im, ← hc, Complex.conj_ofReal]
  let τ : ℝ →+* ℝ :=
    { toFun := fun a => (σ a).re
      map_one' := by simp
      map_mul' := fun a b => by simp [Complex.mul_re, him]
      map_zero' := by simp
      map_add' := fun a b => by simp [Complex.add_re] }
  have hτ : τ = RingHom.id ℝ := Subsingleton.elim _ _
  have hreal : ∀ a : ℝ, σ a = a := fun a => by
    apply Complex.ext
    · exact congrArg (fun φ : ℝ →+* ℝ => φ a) hτ
    · simp [him]
  ext z
  conv_lhs => rw [← Complex.re_add_im z]
  simp only [map_add, map_mul, hreal, hi, RingHom.id_apply]
  exact Complex.re_add_im z

/-- With conjugation alone, the scalar endomorphisms are the identity and conjugation. -/
theorem complex_ringHom_of_conj (σ : ℂ →+* ℂ)
    (hc : ∀ z, σ (starRingEnd ℂ z) = starRingEnd ℂ (σ z)) :
    σ = RingHom.id ℂ ∨ σ = starRingEnd ℂ := by
  have hsq : σ Complex.I ^ 2 = Complex.I ^ 2 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hi | hi
  · exact Or.inl (complex_ringHom_eq_id_of_conj_of_I σ hc hi)
  · right
    have h1 : (starRingEnd ℂ).comp σ = RingHom.id ℂ := by
      apply complex_ringHom_eq_id_of_conj_of_I
      · intro z; simp [hc]
      · simp [hi]
    ext z
    have := RingHom.congr_fun h1 z
    simp only [RingHom.comp_apply, RingHom.id_apply] at this
    conv_rhs => rw [← this]
    rw [Complex.conj_conj]

/-- **Theorem 7.5** (finite-signature rigidification of complex scalars): Token maps
`Q_ℂ^†(V) → Q_ℂ^†(W)` are exactly `id ⊔ f` with `f` complex linear. -/
theorem complexRep_hom_iff {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (h : V ⊕ ℂ → W ⊕ ℂ) :
    TokenClass.IsHom (ComplexRep V) (ComplexRep W) h ↔ ∃ f : V →ₗ[ℂ] W, h = Sum.map f id := by
  constructor
  · intro hh
    have hS : TokenClass.IsHom (ScalarRep ℂ V) (ScalarRep ℂ W) h := by
      intro (w : Word (V ⊕ ℂ) ScalarLabel) hw
      have this : wordMap h (relabelWord ComplexLabel.base w) ∈ (ComplexRep W).heap :=
        hh (relabelWord ComplexLabel.base w) (Or.inl (Or.inl ⟨w, hw, rfl⟩))
      rw [← relabelWord_wordMap] at this
      rcases this with (⟨u, hu, hu'⟩ | ⟨z, hz⟩) | hz
      · have := relabelWord_injective (fun _ _ h => ComplexLabel.base.inj h) hu'
        exact this ▸ hu
      · exact absurd hz (relabelWord_ne_cons_inr _ _ _ (fun e => by simp) _)
      · exact absurd hz (relabelWord_ne_cons_inr _ _ _ (fun e => by simp) _)
    obtain ⟨σ, f, rfl, ⟨σ', rfl⟩, ⟨f', rfl⟩, hact⟩ := (scalarRep_hom_iff h).mp hS
    have hc : ∀ z, σ' (starRingEnd ℂ z) = starRingEnd ℂ (σ' z) := fun z => by
      have := hh [Sum.inr .conj, Sum.inl (Sum.inr z), Sum.inl (Sum.inr (starRingEnd ℂ z))]
        (Or.inl (Or.inr ⟨z, rfl⟩))
      change [Sum.inr ComplexLabel.conj, Sum.inl (Sum.inr (σ' z)),
        Sum.inl (Sum.inr (σ' (starRingEnd ℂ z)))] ∈ (ComplexRep W).heap at this
      rcases this with (⟨u, -, hu⟩ | ⟨z', hz'⟩) | hz'
      · exact absurd hu (relabelWord_ne_cons_inr _ _ _ (fun e => by simp) _)
      · simp only [List.cons.injEq, Sum.inl.injEq, Sum.inr.injEq, and_true, true_and] at hz'
        rw [hz'.2, hz'.1]
      · simp at hz'
    have hi : σ' Complex.I = Complex.I := by
      have := hh [Sum.inr .imagUnit, Sum.inl (Sum.inr Complex.I)] (Or.inr rfl)
      change [Sum.inr ComplexLabel.imagUnit, Sum.inl (Sum.inr (σ' Complex.I))] ∈
        (ComplexRep W).heap at this
      rcases this with (⟨u, -, hu⟩ | ⟨z', hz'⟩) | hz'
      · exact absurd hu (relabelWord_ne_cons_inr _ _ _ (fun e => by simp) _)
      · simp at hz'
      · simpa using hz'
    have hσ : σ' = RingHom.id ℂ := complex_ringHom_eq_id_of_conj_of_I σ' hc hi
    subst hσ
    exact ⟨{ toFun := f'
             map_add' := map_add f'
             map_smul' := fun a v => by simpa using hact a v }, rfl⟩
  · rintro ⟨f, rfl⟩
    intro w hw
    rcases hw with (⟨u, hu, rfl⟩ | ⟨z, rfl⟩) | rfl
    · have key : relabelWord ComplexLabel.base (wordMap (Sum.map (⇑f) id) u) ∈ (ComplexRep W).heap :=
        Or.inl (Or.inl ⟨_, (ScalarRep.ofLinear f).preserves u hu, rfl⟩)
      rw [relabelWord_wordMap] at key
      exact key
    · exact Or.inl (Or.inr ⟨z, rfl⟩)
    · exact Or.inr rfl
/-- The record-length bounds of Theorem 7.5: every record of `Q_ℂ^†(V)` has length ≤ 4. -/
theorem complexRep_record_length {V : Type} [AddCommGroup V] [Module ℂ V]
    (w : Word (V ⊕ ℂ) ComplexLabel) (hw : w ∈ (ComplexRep V).heap) : w.length ≤ 4 := by
  rcases hw with (⟨u, hu, rfl⟩ | ⟨z, rfl⟩) | rfl
  · simpa [relabelWord] using scalarRep_record_length u hu
  · simp
  · simp

open Cardinal in
/-- **Proposition 7.6** (countably many scalar names do not suffice): for every countable
`K ⊆ ℂ`, the pure field `ℂ` with constants naming `K` has a nonidentity automorphism. -/
theorem complex_countable_names_insufficient (K : Set ℂ) (hK : K.Countable) :
    ∃ σ : ℂ ≃+* ℂ, (∀ z ∈ K, σ z = z) ∧ σ ≠ RingEquiv.refl ℂ := by
  classical
  let R : Subfield ℂ := Subfield.closure K
  have hR : #R ≤ ℵ₀ := by
    refine (Subfield.cardinalMk_closure_le_max K).trans (max_le ?_ le_rfl)
    exact Cardinal.mk_le_aleph0_iff.mpr hK.to_subtype
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R ℂ
  have hc : ℵ₀ < #ℂ := by rw [Cardinal.mk_complex]; exact aleph0_lt_continuum
  have hcard : #ℂ = #s :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hR hc
  have hnt : Nontrivial s := by
    rw [← Cardinal.one_lt_iff_nontrivial, ← hcard, Cardinal.mk_complex]
    exact one_lt_aleph0.trans aleph0_lt_continuum
  obtain ⟨b₁, b₂, hb⟩ := exists_pair_ne s
  have := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  set A := Algebra.adjoin R (Set.range ((↑) : s → ℂ)) with hA
  let E : A ≃ₐ[R] A :=
    (hs.1.aevalEquiv.symm.trans (MvPolynomial.renameEquiv R (Equiv.swap b₁ b₂))).trans
      hs.1.aevalEquiv
  let σ : ℂ ≃+* ℂ := IsAlgClosure.equivOfEquiv ℂ ℂ E.toRingEquiv
  refine ⟨σ, fun z hz => ?_, ?_⟩
  · have h1 : z = algebraMap A ℂ (algebraMap R A ⟨z, Subfield.subset_closure hz⟩) := rfl
    rw [h1]
    show (IsAlgClosure.equivOfEquiv ℂ ℂ E.toRingEquiv) _ = _
    rw [IsAlgClosure.equivOfEquiv_algebraMap, AlgEquiv.coe_toRingEquiv, AlgEquiv.commutes]
  · intro h
    have h1 : (b₁ : ℂ) = algebraMap A ℂ (hs.1.aevalEquiv (MvPolynomial.X b₁)) := by
      rw [AlgebraicIndependent.algebraMap_aevalEquiv, MvPolynomial.aeval_X]
    have h2 : σ b₁ = b₂ := by
      show (IsAlgClosure.equivOfEquiv ℂ ℂ E.toRingEquiv) b₁ = b₂
      rw [h1, IsAlgClosure.equivOfEquiv_algebraMap]
      simp only [E, AlgEquiv.coe_toRingEquiv, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, MvPolynomial.renameEquiv_apply,
        MvPolynomial.rename_X, Equiv.swap_apply_left]
      rw [AlgebraicIndependent.algebraMap_aevalEquiv, MvPolynomial.aeval_X]
    rw [h] at h2
    exact hb (Subtype.ext h2)

/-! ### Finite fields (§7.5) -/

section finiteField
variable {F : Type u} [Field F] [Fintype F]

/-- `End(F_q) = Aut(F_q)`: a unital endomorphism of a finite field is bijective. -/
theorem finiteField_ringHom_bijective (σ : F →+* F) : Function.Bijective σ :=
  Finite.injective_iff_bijective.mp σ.injective

/-- Every ring endomorphism of `F` is a `ZMod p`-algebra endomorphism (the prime field is rigid). -/
def ringHomEquivAlgHom (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F] :
    (F →+* F) ≃ (F →ₐ[ZMod p] F) where
  toFun σ :=
    { σ with
      commutes' := fun r =>
        RingHom.congr_fun
          (RingHom.ext_zmod (σ.comp (algebraMap (ZMod p) F)) (algebraMap (ZMod p) F)) r }
  invFun φ := φ.toRingHom
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype F] in
@[simp] theorem ringHomEquivAlgHom_apply (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F]
    (σ : F →+* F) (x : F) : ringHomEquivAlgHom p σ x = σ x := rfl

omit [Fintype F] in
theorem ringHomEquivAlgHom_id (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F] :
    ringHomEquivAlgHom p (RingHom.id F) = AlgHom.id (ZMod p) F := rfl

omit [Fintype F] in
theorem coe_frobeniusAlgHom_eq (p : ℕ) [Fact p.Prime] [CharP F p] [Algebra (ZMod p) F] :
    ⇑(FiniteField.frobeniusAlgHom (ZMod p) F) = ⇑(frobenius F p) := by
  funext x
  rw [FiniteField.coe_frobeniusAlgHom, ZMod.card, frobenius_def]

/-- `End(F_q) = ⟨φ_p⟩` is cyclic of order `n = [F_q : F_p]`. -/
theorem finiteField_end_card (p : ℕ) [Fact p.Prime] [CharP F p] [Algebra (ZMod p) F] :
    Nat.card (F →+* F) = Module.finrank (ZMod p) F ∧
      ∀ σ : F →+* F, ∃ m : ℕ, σ = (frobenius F p) ^ m := by
  refine ⟨?_, fun σ => ?_⟩
  · rw [Nat.card_congr (ringHomEquivAlgHom p)]
    exact FiniteField.natCard_algHom_of_finrank_dvd dvd_rfl
  · obtain ⟨m, hm⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) F).2 (ringHomEquivAlgHom p σ)
    refine ⟨m.1, ?_⟩
    ext x
    have := congrArg (fun φ : F →ₐ[ZMod p] F => φ x) hm
    simp only [AlgHom.coe_pow, coe_frobeniusAlgHom_eq, ringHomEquivAlgHom_apply] at this
    rw [RingHom.coe_pow]
    exact this.symm

omit [Fintype F] in
/-- **Proposition 7.7** (one named field generator restores linearity): a unital endomorphism
of `F_q` fixing a generator `α` with `F_p(α) = F_q` is the identity. -/
theorem finiteField_named_generator_rigid (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F] (α : F)
    (hα : Algebra.adjoin (ZMod p) {α} = ⊤) (σ : F →+* F) (hσ : σ α = α) : σ = RingHom.id F := by
  have : ringHomEquivAlgHom p σ = AlgHom.id (ZMod p) F := by
    apply AlgHom.ext_of_adjoin_eq_top hα
    intro x hx
    rw [Set.mem_singleton_iff.mp hx, ringHomEquivAlgHom_apply, AlgHom.id_apply]
    exact hσ
  exact (ringHomEquivAlgHom p).injective (this.trans (ringHomEquivAlgHom_id p).symm)

/-- Such a generator exists: a generator of the cyclic group `F_q^×`. -/
theorem finiteField_exists_generator (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F] :
    ∃ α : F, Algebra.adjoin (ZMod p) {α} = ⊤ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  refine ⟨g, eq_top_iff.mpr fun x _ => ?_⟩
  by_cases hx : x = 0
  · rw [hx]; exact Subalgebra.zero_mem _
  · obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.mpr (hg (Units.mk0 x hx)))
    have hn' : g ^ n = Units.mk0 x hx := hn
    have : x = (g : F) ^ n := by
      rw [← Units.val_pow_eq_pow_val, hn', Units.val_mk0]
    rw [this]
    exact Subalgebra.pow_mem (Algebra.adjoin (ZMod p) {(g : F)})
      (Algebra.subset_adjoin (Set.mem_singleton _)) n

omit [Fintype F] in
/-- **Remark 7.8**: every field endomorphism commutes with Frobenius, so recording the graph
of `φ_p` imposes no new condition. -/
theorem ringHom_comm_frobenius (p : ℕ) [Fact p.Prime] [CharP F p] (σ : F →+* F) (a : F) :
    σ (a ^ p) = (σ a) ^ p := map_pow σ a p

end finiteField

end AT

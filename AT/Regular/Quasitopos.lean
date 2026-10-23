import AT.Regular.Closure

/-!
# Dependent products, strong subobjects and the quasitopos theorem (paper §5.4)

* `AT.IsQuasitopos` — finitely complete and cocomplete, locally cartesian closed, with a
  classifier for strong subobjects (the standard definition used in the paper).
* `AT.TokenClass.depProd` — the dependent product `Π_p(q)` with heap (5.6).
* `AT.TokenClass.omega` — `Ω = ({0,1}, E, F_E({0,1}))`.
* **Theorem 5.5** (`AT.RegTS.isQuasitopos` and companions): `RegTS_E` is an elementary
  quasitopos; monos/epis are injective/surjective carrier maps; strong monos are exactly the
  induced embeddings.
* **Remark 5.6**: the base condition is essential; `RegTS_E` is not a topos.
-/

universe u v w

namespace AT

open CategoryTheory Limits

/-! ### Elementary quasitoposes -/

section quasitopos
variable (C : Type u) [Category.{v} C]

/-- A classifier for strong subobjects: a strong mono `⊤ : 1 → Ω` such that every strong
mono `m : U → X` is the pullback of `⊤` along a unique `χ : X → Ω`. -/
structure StrongSubobjectClassifier [HasTerminal C] where
  Ω : C
  truth : ⊤_ C ⟶ Ω
  truth_strongMono : StrongMono truth
  classify : ∀ {U X : C} (m : U ⟶ X) [StrongMono m],
    ∃! χ : X ⟶ Ω, IsPullback m (terminal.from U) χ truth

/-- An elementary quasitopos: finite limits, finite colimits, local cartesian closure and a
classifier for strong subobjects (paper §5.4, cf. Parker §2.4). -/
class IsQuasitopos : Prop where
  [hasFiniteLimits : HasFiniteLimits C]
  [hasFiniteColimits : HasFiniteColimits C]
  locallyCartesianClosed : ∀ X : C, ∃ _ : CartesianMonoidalCategory (Over X), Nonempty (MonoidalClosed (Over X))
  classifier : Nonempty (StrongSubobjectClassifier C)

end quasitopos

variable {E : Type v}

/-! ### Core-only words -/

section coreOnly
variable {A B : Type u}

lemma coreOnly_nil : CoreOnly ([] : Word A E) := fun _ h => by simp at h

lemma coreOnly_cons_iff (x : A ⊕ E) (w : Word A E) :
    CoreOnly (x :: w) ↔ x.isRight = true ∧ CoreOnly w := by
  simp [CoreOnly]

lemma wordMap_eq_of_coreOnly {f g : A → B} {w : Word A E} (hw : CoreOnly w) :
    wordMap f w = wordMap g w := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [coreOnly_cons_iff] at hw
    rw [wordMap_cons, wordMap_cons, ih hw.2]
    cases x with
    | inl a => simp at hw
    | inr e => rfl

lemma eq_of_coreOnly_of_shape_eq {u v : Word A E} (hu : CoreOnly u) (hv : CoreOnly v)
    (h : shape u = shape v) : u = v := by
  induction u generalizing v with
  | nil => cases v with
    | nil => rfl
    | cons y v => cases y <;> simp [shape] at h
  | cons x u ih =>
    cases v with
    | nil => cases x <;> simp [shape] at h
    | cons y v =>
      rw [coreOnly_cons_iff] at hu hv
      cases x with
      | inl a => simp at hu
      | inr e =>
        cases y with
        | inl b => simp at hv
        | inr e' =>
          simp only [shape, wordMap_cons, Sum.map_inr, id_eq, List.cons.injEq, Sum.inr.injEq] at h
          rw [h.1, ih hu.2 hv.2 h.2]

lemma exists_coreOnly_shape_eq (w : Word A E) (hw : CoreOnly w) :
    ∃ v : Word B E, CoreOnly v ∧ shape v = shape w := by
  induction w with
  | nil => exact ⟨[], coreOnly_nil, rfl⟩
  | cons x w ih =>
    rw [coreOnly_cons_iff] at hw
    obtain ⟨v, hv, hvs⟩ := ih hw.2
    cases x with
    | inl a => simp at hw
    | inr e =>
      refine ⟨Sum.inr e :: v, (coreOnly_cons_iff _ _).2 ⟨rfl, hv⟩, ?_⟩
      simp only [shape, wordMap_cons, Sum.map_inr, id_eq]
      exact congrArg _ hvs

/-- For a core-only word, membership of its shape in `sh(H)` is membership of a core-only word
of the same shape in `H`. -/
lemma shape_mem_image_iff {w : Word A E} (hw : CoreOnly w) (H : Set (Word B E)) :
    shape w ∈ shape '' H ↔ ∃ v ∈ H, CoreOnly v ∧ shape v = shape w := by
  constructor
  · rintro ⟨v, hv, hvs⟩
    refine ⟨v, hv, ?_, hvs⟩
    have : CoreOnly (shape w) := (coreOnly_wordMap_iff _ _).2 hw
    rw [← hvs] at this
    exact (coreOnly_wordMap_iff _ _).1 this
  · rintro ⟨v, hv, -, hvs⟩
    exact ⟨v, hv, hvs⟩

/-- A core-only word's image lies in `H` iff its shape lies in `sh(H)`. -/
lemma wordMap_mem_iff_shape_mem {w : Word A E} (hw : CoreOnly w) (f : A → B) (H : Set (Word B E)) :
    wordMap f w ∈ H ↔ shape w ∈ shape '' H := by
  rw [shape_mem_image_iff hw]
  constructor
  · intro h
    exact ⟨_, h, (coreOnly_wordMap_iff _ _).2 hw, shape_wordMap _ _⟩
  · rintro ⟨v, hv, hvc, hvs⟩
    have : v = wordMap f w :=
      eq_of_coreOnly_of_shape_eq hvc ((coreOnly_wordMap_iff _ _).2 hw) (by rw [hvs, shape_wordMap])
    rwa [← this]

end coreOnly

/-! ### Dependent products (eqs. 5.5–5.6) -/

section depProd
variable {TA TB TX : TokenClass.{u} E} (p : TA ⟶ TB) (q : TX ⟶ TA)

/-- Sections over the fibre `A_b = p⁻¹(b)`: `S_b = {s : A_b → X : q ∘ s = id}`. -/
def TokenClass.sectionsOver (b : TB.carrier) : Type u :=
  {s : {a : TA.carrier // p.toFun a = b} → TX.carrier // ∀ a, q.toFun (s a) = a.1}

/-- `S = ∐_b S_b`, tagged pairs `(b, s)`. -/
abbrev TokenClass.depProdCarrier : Type u := Σ b : TB.carrier, TokenClass.sectionsOver p q b

/-- `r : S → B`. -/
def TokenClass.depProdBase : TokenClass.depProdCarrier p q → TB.carrier := Sigma.fst

/-- The pullback `P = S ×_B A` with its projections `π`, `α` and the evaluation `e`. -/
abbrev TokenClass.depProdPairs : Type u :=
  {x : TokenClass.depProdCarrier p q × TA.carrier // x.1.1 = p.toFun x.2}

def TokenClass.depProdEval (x : TokenClass.depProdPairs p q) : TX.carrier :=
  x.1.1.2.1 ⟨x.1.2, x.2.symm⟩

/-- `W_{p,q} = F_E(α)⁻¹(H_A) ∩ F_E(e)⁻¹(F_E(X) \ H_X)` (eq. 5.5). -/
def TokenClass.depProdFailures : Set (Word (TokenClass.depProdPairs p q) E) :=
  {w | wordMap (fun x => x.1.2) w ∈ TA.heap ∧ wordMap (TokenClass.depProdEval p q) w ∉ TX.heap}

/-- `H_S = F_E(r)⁻¹(H_B) \ F_E(π)(W_{p,q})` (eq. 5.6). -/
def TokenClass.depProdHeap : Set (Word (TokenClass.depProdCarrier p q) E) :=
  {w | wordMap (TokenClass.depProdBase p q) w ∈ TB.heap} \
    (wordMap (fun x => x.1.1) '' TokenClass.depProdFailures p q)

/-- The dependent product object `T_S`. -/
def TokenClass.depProd : TokenClass.{u} E := ⟨_, TokenClass.depProdHeap p q⟩

/-- `r : T_S → T_B` is a Token map (first factor of (5.6)). -/
def TokenClass.depProdHom : TokenClass.depProd p q ⟶ TB :=
  ⟨TokenClass.depProdBase p q, fun _ hw => hw.1⟩

/-- The nullary clause (5.7): `H_S ∩ E^* = {w ∈ E^* : w ∈ H_B ∧ (w ∈ H_A → w ∈ H_X)}`. -/
theorem TokenClass.depProd_coreOnly (w : Word (TokenClass.depProdCarrier p q) E) (hw : CoreOnly w) :
    w ∈ TokenClass.depProdHeap p q ↔
      (wordMap (fun _ => PUnit.unit) w ∈ wordMap (fun _ : TB.carrier => PUnit.unit) '' TB.heap ∧
       (wordMap (fun _ => PUnit.unit) w ∈ wordMap (fun _ : TA.carrier => PUnit.unit) '' TA.heap →
        wordMap (fun _ => PUnit.unit) w ∈ wordMap (fun _ : TX.carrier => PUnit.unit) '' TX.heap)) := by
  change w ∈ TokenClass.depProdHeap p q ↔
    (shape w ∈ shape '' TB.heap ∧ (shape w ∈ shape '' TA.heap → shape w ∈ shape '' TX.heap))
  rw [← wordMap_mem_iff_shape_mem hw (TokenClass.depProdBase p q)]
  unfold TokenClass.depProdHeap
  rw [Set.mem_sdiff, Set.mem_ofPred_eq]
  apply and_congr_right
  intro _
  rw [Set.mem_image, not_exists]
  constructor
  · intro h hA
    by_contra hX
    obtain ⟨v, hv, hvs⟩ := exists_coreOnly_shape_eq (B := TokenClass.depProdPairs p q) w hw
    refine h v ⟨⟨?_, ?_⟩, eq_of_coreOnly_of_shape_eq ((coreOnly_wordMap_iff _ _).2 hv) hw
      (by rw [shape_wordMap, hvs])⟩
    · rw [wordMap_mem_iff_shape_mem hv, hvs]; exact hA
    · rw [wordMap_mem_iff_shape_mem hv, hvs]; exact hX
  · rintro h v ⟨⟨hvA, hvX⟩, hvw⟩
    have hv : CoreOnly v := by
      rw [← coreOnly_wordMap_iff (fun x : TokenClass.depProdPairs p q => x.1.1), hvw]; exact hw
    have hs : shape v = shape w := by rw [← hvw, shape_wordMap]
    rw [wordMap_mem_iff_shape_mem hv, hs] at hvA hvX
    exact hvX (h hvA)

theorem TokenClass.depProd_isRegular [Finite TA.carrier] [Finite TB.carrier] [Finite TX.carrier]
    (hA : TA.IsRegularHeap) (hB : TB.IsRegularHeap) (hX : TX.IsRegularHeap) :
    (TokenClass.depProd p q).IsRegularHeap := by
  have : Finite (TokenClass.depProdPairs p q) := by
    unfold TokenClass.depProdPairs TokenClass.depProdCarrier TokenClass.sectionsOver
    infer_instance
  have hfail : (show Language (TokenClass.depProdPairs p q ⊕ E) from
      TokenClass.depProdFailures p q).IsRegular := by
    have h1 := Language.IsRegular.comap_wordMap (E := E) (fun x : TokenClass.depProdPairs p q => x.1.2) hA
    have h2 := (Language.IsRegular.comap_wordMap (E := E) (TokenClass.depProdEval p q) hX).compl
    exact h1.inf h2
  have hbase := Language.IsRegular.comap_wordMap (E := E) (TokenClass.depProdBase p q) hB
  have himg := (Language.IsRegular.image_wordMap (E := E)
    (fun x : TokenClass.depProdPairs p q => x.1.1) hfail).compl
  exact hbase.inf himg

end depProd

/-- `Ω = ({0,1}, E, F_E({0,1}))`; every carrier function into it is a Token map. -/
def TokenClass.omega (E : Type v) : TokenClass.{u} E := ⟨ULift Bool, Set.univ⟩

/-- The full language is regular. -/
theorem isRegular_univ {α : Type u} : (show Language α from Set.univ).IsRegular :=
  ⟨Unit, inferInstance, ⟨fun _ _ => (), (), Set.univ⟩, by
    ext; simp only [DFA.mem_accepts]; exact ⟨fun _ => Set.mem_univ _, fun _ => Set.mem_univ _⟩⟩

/-- The empty language is regular. -/
theorem isRegular_empty {α : Type u} : (show Language α from (∅ : Set (List α))).IsRegular :=
  ⟨Unit, inferInstance, ⟨fun _ _ => (), (), ∅⟩, by
    ext; simp only [DFA.mem_accepts]; exact ⟨fun h => h, fun h => h⟩⟩

theorem TokenClass.omega_isRegular : (TokenClass.omega.{u} E).IsRegularHeap := isRegular_univ

/-- The singleton object with empty heap, used to detect carrier points. -/
def TokenClass.point (E : Type v) : TokenClass.{u} E := ⟨PUnit, ∅⟩

instance : Finite (TokenClass.point.{u} E).carrier := inferInstanceAs (Finite PUnit)
instance : Finite (TokenClass.omega.{u} E).carrier := inferInstanceAs (Finite (ULift Bool))
instance : Finite (TokenClass.terminal.{u} E).carrier := inferInstanceAs (Finite PUnit)

/-- The map from the point object selecting `a`. -/
def TokenClass.ofPoint {T : TokenClass.{u} E} (a : T.carrier) : TokenClass.point E ⟶ T :=
  TokenClass.homOfEmptyHeap rfl (fun _ => a)

theorem TokenClass.point_isRegular : (TokenClass.point.{u} E).IsRegularHeap := isRegular_empty

/-- Any carrier function into `Ω` is a Token map. -/
def TokenClass.toOmega {T : TokenClass.{u} E} (f : T.carrier → Bool) : T ⟶ TokenClass.omega E :=
  ⟨fun a => ⟨f a⟩, fun _ _ => trivial⟩

/-- `m` is an induced embedding: injective with `H_A = F_E(m)⁻¹(H_B)`. -/
def TokenClass.IsInduced {TA TB : TokenClass.{u} E} (m : TA ⟶ TB) : Prop :=
  Function.Injective m.toFun ∧ TA.heap = wordMap m.toFun ⁻¹' TB.heap

/-! ### Theorem 5.5 in the ambient category -/

theorem TokenClass.mono_iff_injective {TA TB : TokenClass.{u} E} (m : TA ⟶ TB) :
    Mono m ↔ Function.Injective m.toFun := by
  constructor
  · intro hm a₁ a₂ h
    have : TokenClass.ofPoint a₁ ≫ m = TokenClass.ofPoint a₂ ≫ m :=
      TokenClass.Hom.ext (funext fun _ => h)
    have := congrArg (fun k : TokenClass.point E ⟶ TA => k.toFun PUnit.unit) (hm.right_cancellation _ _ this)
    exact this
  · intro hm
    refine ⟨fun g h hgh => TokenClass.Hom.ext (funext fun x => hm ?_)⟩
    exact congrArg (fun k : TokenClass.Hom _ _ => k.toFun x) hgh

theorem TokenClass.epi_iff_surjective {TA TB : TokenClass.{u} E} (m : TA ⟶ TB) :
    Epi m ↔ Function.Surjective m.toFun := by
  classical
  constructor
  · intro hm b
    by_contra hb
    have h : m ≫ TokenClass.toOmega (fun _ => true) =
        m ≫ TokenClass.toOmega (fun b' => decide (∃ a, m.toFun a = b')) :=
      TokenClass.Hom.ext (funext fun a => by
        simp only [comp_toFun, Function.comp, TokenClass.toOmega]
        congr 1; symm; simp)
    have := congrArg (fun k : TB ⟶ TokenClass.omega E => (k.toFun b).down) (hm.left_cancellation _ _ h)
    simp [TokenClass.toOmega] at this
    exact hb this
  · intro hm
    refine ⟨fun g h hgh => TokenClass.Hom.ext (funext fun b => ?_)⟩
    obtain ⟨a, rfl⟩ := hm b
    exact congrArg (fun k : TokenClass.Hom _ _ => k.toFun a) hgh

theorem TokenClass.strongMono_iff_isInduced {TA TB : TokenClass.{u} E} (m : TA ⟶ TB) :
    StrongMono m ↔ TokenClass.IsInduced m := by
  constructor
  · intro hm
    have := hm.mono
    refine ⟨(TokenClass.mono_iff_injective m).1 inferInstance, ?_⟩
    -- factor `m` through the induced heap on the same carrier
    let TI : TokenClass.{u} E := ⟨TA.carrier, wordMap m.toFun ⁻¹' TB.heap⟩
    let u : TA ⟶ TI := ⟨id, fun w hw => by
      show wordMap m.toFun (wordMap id w) ∈ TB.heap
      rw [wordMap_id]; exact m.preserves w hw⟩
    let j : TI ⟶ TB := ⟨m.toFun, fun _ hw => hw⟩
    have : Epi u := (TokenClass.epi_iff_surjective u).2 (fun a => ⟨a, rfl⟩)
    have sq : CommSq (𝟙 TA) u m j := ⟨TokenClass.Hom.ext rfl⟩
    have := hm.rlp u
    obtain ⟨⟨l, hl₁, _⟩⟩ := (HasLiftingProperty.sq_hasLift sq).exists_lift
    have hl : l.toFun = id := by
      have := congrArg TokenClass.Hom.toFun hl₁
      simpa using this
    apply Set.Subset.antisymm
    · intro w hw; exact m.preserves w hw
    · intro w hw
      have := l.preserves w hw
      rwa [hl, wordMap_id] at this
  · rintro ⟨hinj, hheap⟩
    have : Mono m := (TokenClass.mono_iff_injective m).2 hinj
    refine ⟨inferInstance, fun X Y z hz => ⟨fun {uu} {v} sq => ?_⟩⟩
    have hz' := (TokenClass.epi_iff_surjective z).1 hz
    have hsq := congrArg TokenClass.Hom.toFun sq.w
    simp only [comp_toFun] at hsq
    choose pre hpre using hz'
    -- well-definedness of the diagonal
    have key : ∀ x, uu.toFun x = uu.toFun (pre (z.toFun x)) := by
      intro x
      apply hinj
      have h1 := congrFun hsq x
      have h2 := congrFun hsq (pre (z.toFun x))
      simp only [Function.comp] at h1 h2
      rw [h1, h2, hpre]
    let d : Y ⟶ TA := ⟨fun y => uu.toFun (pre y), fun w hw => by
      rw [hheap, Set.mem_preimage, ← Function.comp_apply (f := wordMap m.toFun), ← wordMap_comp]
      have : m.toFun ∘ (fun y => uu.toFun (pre y)) = v.toFun := by
        funext y
        have := congrFun hsq (pre y)
        simp only [Function.comp] at this
        rw [Function.comp_apply, this, hpre]
      rw [this]; exact v.preserves w hw⟩
    exact ⟨⟨⟨d, TokenClass.Hom.ext (funext fun x => (key x).symm),
      TokenClass.Hom.ext (funext fun y => by
        show m.toFun (uu.toFun (pre y)) = v.toFun y
        have := congrFun hsq (pre y)
        simp only [Function.comp] at this
        rw [this, hpre])⟩⟩⟩

/-! ### Concrete pullbacks -/

section pullback
variable {A B C : Type u}

/-- Two words with the same image in `C` lift to a word over the set-theoretic pullback. -/
lemma exists_word_pb (f : A → C) (g : B → C) :
    ∀ (w : Word A E) (v : Word B E), wordMap f w = wordMap g v →
    ∃ u : Word {x : A × B // f x.1 = g x.2} E,
      wordMap (fun x => x.1.1) u = w ∧ wordMap (fun x => x.1.2) u = v
  | [], [], _ => ⟨[], rfl, rfl⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: w, y :: v, h => by
    rw [wordMap_cons, wordMap_cons, List.cons.injEq] at h
    obtain ⟨u, hu1, hu2⟩ := exists_word_pb f g w v h.2
    match x, y, h.1 with
    | Sum.inl a, Sum.inl b, h1 =>
      exact ⟨Sum.inl ⟨(a, b), Sum.inl.inj h1⟩ :: u, by simp [hu1], by simp [hu2]⟩
    | Sum.inr e, Sum.inr e', h1 =>
      obtain rfl : e = e' := by simpa using h1
      exact ⟨Sum.inr e :: u, by simp [hu1], by simp [hu2]⟩
    | Sum.inl _, Sum.inr _, h1 => simp at h1
    | Sum.inr _, Sum.inl _, h1 => simp at h1

variable {TA TB TC : TokenClass.{u} E} (f : TA ⟶ TC) (g : TB ⟶ TC)

/-- The pullback `T_A ×_{T_C} T_B` with heap `F(π₁)⁻¹(H_A) ∩ F(π₂)⁻¹(H_B)`. -/
def TokenClass.pb : TokenClass.{u} E :=
  ⟨{x : TA.carrier × TB.carrier // f.toFun x.1 = g.toFun x.2},
    {w | wordMap (fun x => x.1.1) w ∈ TA.heap ∧ wordMap (fun x => x.1.2) w ∈ TB.heap}⟩

def TokenClass.pbFst : TokenClass.pb f g ⟶ TA := ⟨fun x => x.1.1, fun _ hw => hw.1⟩
def TokenClass.pbSnd : TokenClass.pb f g ⟶ TB := ⟨fun x => x.1.2, fun _ hw => hw.2⟩

theorem TokenClass.pb_condition : TokenClass.pbFst f g ≫ f = TokenClass.pbSnd f g ≫ g :=
  TokenClass.Hom.ext (funext fun x => x.2)

/-- The universal map into the pullback. -/
def TokenClass.pbLift {TZ : TokenClass.{u} E} (u : TZ ⟶ TA) (v : TZ ⟶ TB) (h : u ≫ f = v ≫ g) :
    TZ ⟶ TokenClass.pb f g :=
  ⟨fun z => ⟨(u.toFun z, v.toFun z), congrArg (fun k : TZ ⟶ TC => k.toFun z) h⟩,
    fun w hw => ⟨by erw [wordMap_wordMap]; exact u.preserves w hw,
      by erw [wordMap_wordMap]; exact v.preserves w hw⟩⟩

/-- The symmetry `T_A ×_{T_C} T_B ≅ T_B ×_{T_C} T_A`. -/
def TokenClass.pbSwap : TokenClass.pb f g ⟶ TokenClass.pb g f :=
  ⟨fun x => ⟨(x.1.2, x.1.1), x.2.symm⟩,
    fun w hw => ⟨by erw [wordMap_wordMap]; exact hw.2, by erw [wordMap_wordMap]; exact hw.1⟩⟩

def TokenClass.pbSwapIso : TokenClass.pb f g ≅ TokenClass.pb g f where
  hom := TokenClass.pbSwap f g
  inv := TokenClass.pbSwap g f

theorem TokenClass.pb_isRegular [Finite E] (hA : TA.IsRegularHeap) (hB : TB.IsRegularHeap) :
    (TokenClass.pb f g).IsRegularHeap :=
  (Language.IsRegular.comap_wordMap (E := E) (fun x : (TokenClass.pb f g).carrier => x.1.1) hA).inf
    (Language.IsRegular.comap_wordMap (E := E) (fun x : (TokenClass.pb f g).carrier => x.1.2) hB)

end pullback

/-! ### The pullback functor and its left adjoint -/

section pullbackFunctor
variable {TY TX : TokenClass.{u} E} (g : TY ⟶ TX)

/-- Pullback along `g : T_Y ⟶ T_X` as a functor `Over T_X ⥤ Over T_Y`. -/
def TokenClass.pullbackF : Over TX ⥤ Over TY where
  obj Z := Over.mk (TokenClass.pbSnd Z.hom g)
  map {Z Z'} k := Over.homMk
    (TokenClass.pbLift Z'.hom g (TokenClass.pbFst Z.hom g ≫ k.left) (TokenClass.pbSnd Z.hom g)
      (TokenClass.Hom.ext (funext fun x =>
        (congrArg (fun m : Z.left ⟶ TX => m.toFun x.1.1) (Over.w k)).trans x.2)))
    (TokenClass.Hom.ext rfl)
  map_id _ := Over.OverMorphism.ext (TokenClass.Hom.ext rfl)
  map_comp _ _ := Over.OverMorphism.ext (TokenClass.Hom.ext rfl)

/-- `Σ_g ⊣ g^*`. -/
def TokenClass.mapPullbackAdj' : Over.map g ⊣ TokenClass.pullbackF g :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun W Z =>
        { toFun := fun k => Over.homMk
            (TokenClass.pbLift Z.hom g k.left W.hom (Over.w k)) (TokenClass.Hom.ext rfl)
          invFun := fun m => Over.homMk (m.left ≫ TokenClass.pbFst Z.hom g)
            (TokenClass.Hom.ext (funext fun w =>
              (m.left.toFun w).2.trans
                (congrArg (fun k : W.left ⟶ TY => g.toFun (k.toFun w)) (Over.w m))))
          left_inv := fun _ => Over.OverMorphism.ext (TokenClass.Hom.ext rfl)
          right_inv := fun m => Over.OverMorphism.ext (TokenClass.Hom.ext (funext fun w =>
            Subtype.ext (Prod.ext rfl (congrArg (fun k : W.left ⟶ TY => k.toFun w) (Over.w m)).symm))) }
      homEquiv_naturality_left_symm := fun _ _ => Over.OverMorphism.ext (TokenClass.Hom.ext rfl)
      homEquiv_naturality_right := fun _ _ => Over.OverMorphism.ext (TokenClass.Hom.ext rfl) }

instance TokenClass.chosenPullbacksAlong : ChosenPullbacksAlong g where
  pullback := TokenClass.pullbackF g
  mapPullbackAdj := TokenClass.mapPullbackAdj' g

instance TokenClass.chosenPullbacks : ChosenPullbacks (TokenClass.{u} E) :=
  fun g => TokenClass.chosenPullbacksAlong g

end pullbackFunctor

/-! ### The dependent-product functor `Π_p` and the adjunction `p^* ⊣ Π_p` -/

section pushforward
variable {TA TB : TokenClass.{u} E} (p : TA ⟶ TB)

/-- Extensionality for elements `(b, s)` of the dependent-product carrier. -/
lemma TokenClass.depProd_ext {TX : TokenClass.{u} E} {q : TX ⟶ TA}
    {x y : TokenClass.depProdCarrier p q} (h1 : x.1 = y.1)
    (h2 : ∀ a (ha : p.toFun a = x.1) (hb : p.toFun a = y.1), x.2.1 ⟨a, ha⟩ = y.2.1 ⟨a, hb⟩) :
    x = y := by
  obtain ⟨b, s⟩ := x
  obtain ⟨b', s'⟩ := y
  cases h1
  have : s = s' := Subtype.ext (funext fun a => h2 a.1 a.2 a.2)
  rw [this]

lemma TokenClass.depProd_snd_congr {TX : TokenClass.{u} E} {q : TX ⟶ TA}
    {x y : TokenClass.depProdCarrier p q} (h : x = y) (a : TA.carrier)
    (ha : p.toFun a = x.1) (hb : p.toFun a = y.1) : x.2.1 ⟨a, ha⟩ = y.2.1 ⟨a, hb⟩ := by
  subst h; rfl

/-- Action of `Π_p` on a morphism `k : q ⟶ q'` over `T_A`: `(b, s) ↦ (b, k ∘ s)`. -/
def TokenClass.depProdMapFun {TX TX' : TokenClass.{u} E} {q : TX ⟶ TA} {q' : TX' ⟶ TA}
    (k : TX ⟶ TX') (hk : k ≫ q' = q) :
    TokenClass.depProdCarrier p q → TokenClass.depProdCarrier p q' :=
  fun x => ⟨x.1, ⟨fun a => k.toFun (x.2.1 a), fun a => by
    have := congrArg (fun m : TX ⟶ TA => m.toFun (x.2.1 a)) hk
    exact this.trans (x.2.2 a)⟩⟩

theorem TokenClass.depProdMapFun_preserves {TX TX' : TokenClass.{u} E} {q : TX ⟶ TA}
    {q' : TX' ⟶ TA} (k : TX ⟶ TX') (hk : k ≫ q' = q)
    (w : Word (TokenClass.depProdCarrier p q) E) (hw : w ∈ TokenClass.depProdHeap p q) :
    wordMap (TokenClass.depProdMapFun p k hk) w ∈ TokenClass.depProdHeap p q' := by
  refine ⟨?_, ?_⟩
  · show wordMap _ (wordMap _ w) ∈ TB.heap
    erw [wordMap_wordMap]; exact hw.1
  · rintro ⟨v, hv, hvw⟩
    obtain ⟨u, hu1, hu2⟩ :=
      exists_word_pb (TokenClass.depProdMapFun p k hk) (fun x => x.1.1) w v hvw.symm
    let lift : {x : TokenClass.depProdCarrier p q × TokenClass.depProdPairs p q' //
        TokenClass.depProdMapFun p k hk x.1 = x.2.1.1} → TokenClass.depProdPairs p q :=
      fun x => ⟨(x.1.1, x.1.2.1.2), by
        have h1 := x.1.2.2
        have h2 := congrArg Sigma.fst x.2
        exact h2.trans h1⟩
    apply hw.2
    refine ⟨wordMap lift u, ⟨?_, ?_⟩, ?_⟩
    · erw [wordMap_wordMap]
      have := hv.1
      rw [← hu2] at this
      erw [wordMap_wordMap] at this
      exact this
    · intro hX
      apply hv.2
      rw [← hu2]
      erw [wordMap_wordMap] at hX ⊢
      have := k.preserves _ hX
      erw [wordMap_wordMap] at this
      have hc : wordMap (TokenClass.depProdEval p q' ∘ fun x => x.1.2) u =
          wordMap (k.toFun ∘ TokenClass.depProdEval p q ∘ lift) u :=
        wordMap_congr (fun x _ => TokenClass.depProd_snd_congr p x.2.symm _ x.1.2.2.symm
        (x.1.2.2.symm.trans (congrArg Sigma.fst x.2).symm))
      exact hc ▸ this
    · erw [wordMap_wordMap]; exact hu1

/-- The dependent-product functor `Π_p : Over T_A ⥤ Over T_B`. -/
def TokenClass.pushforward : Over TA ⥤ Over TB where
  obj q := Over.mk (TokenClass.depProdHom p q.hom)
  map k := Over.homMk
    ⟨TokenClass.depProdMapFun p k.left (Over.w k), TokenClass.depProdMapFun_preserves p k.left (Over.w k)⟩
    (TokenClass.Hom.ext rfl)
  map_id _ := Over.OverMorphism.ext (TokenClass.Hom.ext rfl)
  map_comp _ _ := Over.OverMorphism.ext (TokenClass.Hom.ext rfl)

section curry
variable {TX : TokenClass.{u} E} (Z : Over TB) (q : TX ⟶ TA)

/-- Currying: a map `p^* Z ⟶ q` over `T_A` gives `z ↦ (Z z, a ↦ g(z, a))`. -/
def TokenClass.curryFun (g : TokenClass.pb Z.hom p ⟶ TX) (hg : g ≫ q = TokenClass.pbSnd Z.hom p) :
    Z.left.carrier → TokenClass.depProdCarrier p q :=
  fun z => ⟨Z.hom.toFun z, ⟨fun a => g.toFun ⟨(z, a.1), a.2.symm⟩,
    fun a => congrArg (fun m : TokenClass.pb Z.hom p ⟶ TA => m.toFun ⟨(z, a.1), a.2.symm⟩) hg⟩⟩

theorem TokenClass.curryFun_preserves (g : TokenClass.pb Z.hom p ⟶ TX)
    (hg : g ≫ q = TokenClass.pbSnd Z.hom p) (w : Word Z.left.carrier E) (hw : w ∈ Z.left.heap) :
    wordMap (TokenClass.curryFun p Z q g hg) w ∈ TokenClass.depProdHeap p q := by
  refine ⟨?_, ?_⟩
  · show wordMap _ (wordMap _ w) ∈ TB.heap
    erw [wordMap_wordMap]; exact Z.hom.preserves w hw
  · rintro ⟨v, hv, hvw⟩
    obtain ⟨u, hu1, hu2⟩ :=
      exists_word_pb (TokenClass.curryFun p Z q g hg) (fun x => x.1.1) w v hvw.symm
    let lift : {x : Z.left.carrier × TokenClass.depProdPairs p q //
        TokenClass.curryFun p Z q g hg x.1 = x.2.1.1} → (TokenClass.pb Z.hom p).carrier :=
      fun x => ⟨(x.1.1, x.1.2.1.2), (congrArg Sigma.fst x.2).trans x.1.2.2⟩
    have hu : wordMap lift u ∈ (TokenClass.pb Z.hom p).heap := by
      refine ⟨?_, ?_⟩
      · erw [wordMap_wordMap]; exact hu1 ▸ hw
      · erw [wordMap_wordMap]
        have := hv.1
        rw [← hu2] at this
        erw [wordMap_wordMap] at this
        exact this
    have := g.preserves _ hu
    erw [wordMap_wordMap] at this
    apply hv.2
    rw [← hu2]
    erw [wordMap_wordMap]
    have hc : wordMap (TokenClass.depProdEval p q ∘ fun x => x.1.2) u =
        wordMap (g.toFun ∘ lift) u :=
      wordMap_congr (fun x _ => TokenClass.depProd_snd_congr p x.2.symm _ x.1.2.2.symm
        (x.1.2.2.symm.trans (congrArg Sigma.fst x.2).symm))
    exact hc ▸ this

/-- Uncurrying: a map `Z ⟶ Π_p q` over `T_B` gives `(z, a) ↦ (h z).s(a)`. -/
def TokenClass.uncurryFun (h : Z.left ⟶ TokenClass.depProd p q)
    (hh : h ≫ TokenClass.depProdHom p q = Z.hom) :
    (TokenClass.pb Z.hom p).carrier → TX.carrier :=
  fun x => (h.toFun x.1.1).2.1 ⟨x.1.2,
    x.2.symm.trans (congrArg (fun m : Z.left ⟶ TB => m.toFun x.1.1) hh).symm⟩

theorem TokenClass.uncurryFun_preserves (h : Z.left ⟶ TokenClass.depProd p q)
    (hh : h ≫ TokenClass.depProdHom p q = Z.hom) (u : Word (TokenClass.pb Z.hom p).carrier E)
    (hu : u ∈ (TokenClass.pb Z.hom p).heap) :
    wordMap (TokenClass.uncurryFun p Z q h hh) u ∈ TX.heap := by
  by_contra hX
  let toPairs : (TokenClass.pb Z.hom p).carrier → TokenClass.depProdPairs p q :=
    fun x => ⟨(h.toFun x.1.1, x.1.2),
      (congrArg (fun m : Z.left ⟶ TB => m.toFun x.1.1) hh).trans x.2⟩
  have hS := h.preserves _ hu.1
  apply hS.2
  refine ⟨wordMap toPairs u, ⟨?_, ?_⟩, ?_⟩
  · erw [wordMap_wordMap]; exact hu.2
  · erw [wordMap_wordMap]; exact hX
  · erw [wordMap_wordMap, wordMap_wordMap]; rfl

end curry

/-- The adjunction `p^* ⊣ Π_p` (eq. 5.7 of the paper). -/
def TokenClass.pullbackPushforwardAdj : TokenClass.pullbackF p ⊣ TokenClass.pushforward p :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun Z q =>
        { toFun := fun g => Over.homMk
            ⟨TokenClass.curryFun p Z q.hom g.left (Over.w g),
              TokenClass.curryFun_preserves p Z q.hom g.left (Over.w g)⟩
            (TokenClass.Hom.ext rfl)
          invFun := fun h => Over.homMk
            ⟨TokenClass.uncurryFun p Z q.hom h.left (Over.w h),
              TokenClass.uncurryFun_preserves p Z q.hom h.left (Over.w h)⟩
            (TokenClass.Hom.ext (funext fun x => (h.left.toFun x.1.1).2.2 _))
          left_inv := fun _ => Over.OverMorphism.ext (TokenClass.Hom.ext rfl)
          right_inv := fun h => Over.OverMorphism.ext (TokenClass.Hom.ext (funext fun z =>
            TokenClass.depProd_ext p
              (congrArg (fun m : Z.left ⟶ TB => m.toFun z) (Over.w h)).symm
              (fun _ _ _ => rfl))) }
      homEquiv_naturality_left_symm := fun _ _ => Over.OverMorphism.ext (TokenClass.Hom.ext rfl)
      homEquiv_naturality_right := fun _ _ => Over.OverMorphism.ext (TokenClass.Hom.ext rfl) }

end pushforward

/-! ### Local cartesian closure -/

section lcc
variable {TX : TokenClass.{u} E}

/-- The binary fan `Y ×_X Z := Σ_{Y}(Y^* Z)` in `Over T_X`. -/
abbrev TokenClass.overFan (Y Z : Over TX) : BinaryFan Y Z :=
  BinaryFan.mk (P := (Over.map Y.hom).obj ((TokenClass.pullbackF Y.hom).obj Z))
    (Over.homMk (TokenClass.pbSnd Z.hom Y.hom) (TokenClass.Hom.ext rfl))
    (Over.homMk (TokenClass.pbFst Z.hom Y.hom) (TokenClass.pb_condition Z.hom Y.hom))

def TokenClass.overFanIsLimit (Y Z : Over TX) : IsLimit (TokenClass.overFan Y Z) :=
  BinaryFan.IsLimit.mk _
    (fun {W} u v => Over.homMk
      (TokenClass.pbLift Z.hom Y.hom v.left u.left (by rw [Over.w u, Over.w v]))
      (TokenClass.Hom.ext (funext fun w => congrArg (fun m : W.left ⟶ TX => m.toFun w) (Over.w u))))
    (fun _ _ => Over.OverMorphism.ext (TokenClass.Hom.ext rfl))
    (fun _ _ => Over.OverMorphism.ext (TokenClass.Hom.ext rfl))
    (fun u v m h1 h2 => Over.OverMorphism.ext (TokenClass.Hom.ext (funext fun w =>
      Subtype.ext (Prod.ext
        (congrArg (fun k : _ ⟶ Z => k.left.toFun w) h2)
        (congrArg (fun k : _ ⟶ Y => k.left.toFun w) h1)))))

/-- The cartesian monoidal structure on `Over T_X` given by concrete pullbacks. -/
@[instance_reducible]
def TokenClass.overCMC (TX : TokenClass.{u} E) : CartesianMonoidalCategory (Over TX) :=
  CartesianMonoidalCategory.ofChosenFiniteProducts
    ⟨Limits.asEmptyCone (Over.mk (𝟙 TX)),
      Limits.IsTerminal.ofUniqueHom (fun Y => Over.homMk Y.hom)
        fun Y m => Over.OverMorphism.ext (by simpa using m.w)⟩
    (fun Y Z => ⟨_, TokenClass.overFanIsLimit Y Z⟩)

attribute [local instance] TokenClass.overCMC

open MonoidalCategory in
/-- `Y ⊗ -` is `Σ_Y ∘ Y^*` on the nose. -/
def TokenClass.tensorLeftIso (Y : Over TX) :
    TokenClass.pullbackF Y.hom ⋙ Over.map Y.hom ≅ tensorLeft Y :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => Over.OverMorphism.ext (TokenClass.Hom.ext rfl))

open MonoidalCategory in
instance TokenClass.overClosed (Y : Over TX) : Closed Y where
  rightAdj := TokenClass.pullbackF Y.hom ⋙ TokenClass.pushforward Y.hom
  adj := ((TokenClass.pullbackPushforwardAdj Y.hom).comp (TokenClass.mapPullbackAdj' Y.hom)).ofNatIsoLeft
    (TokenClass.tensorLeftIso Y)

instance TokenClass.overMonoidalClosed (TX : TokenClass.{u} E) : MonoidalClosed (Over TX) where

end lcc

/-- The dependent product is right adjoint to pullback: `Hom_{/T_A}(p^* z, q) ≅ Hom_{/T_B}(z, r)`. -/
theorem TokenClass.depProd_isRightAdjoint {TA TB : TokenClass.{u} E} (p : TA ⟶ TB) :
    Nonempty ((Over.pullback p).IsLeftAdjoint) :=
  ⟨⟨⟨TokenClass.pushforward p, ⟨(TokenClass.pullbackPushforwardAdj p).ofNatIsoLeft
    (ChosenPullbacksAlong.pullbackIsoOverPullback p)⟩⟩⟩⟩

/-- `TS_E` is locally cartesian closed. -/
theorem TokenClass.locallyCartesianClosed (X : TokenClass.{u} E) :
    ∃ _ : CartesianMonoidalCategory (Over X), Nonempty (MonoidalClosed (Over X)) :=
  ⟨TokenClass.overCMC X, ⟨TokenClass.overMonoidalClosed X⟩⟩

/-- The chosen terminal object of `TS_E` has a one-point carrier. -/
noncomputable def TokenClass.terminalCarrierEquiv : (⊤_ TokenClass.{u} E).carrier ≃ PUnit.{u+1} :=
  let i : ⊤_ TokenClass.{u} E ≅ TokenClass.terminal E :=
    Limits.terminalIsTerminal.uniqueUpToIso TokenClass.terminalIsTerminal
  { toFun := i.hom.toFun
    invFun := i.inv.toFun
    left_inv := fun x => congrArg (fun k : ⊤_ TokenClass.{u} E ⟶ ⊤_ TokenClass.{u} E => k.toFun x) i.hom_inv_id
    right_inv := fun x => congrArg (fun k : TokenClass.terminal E ⟶ TokenClass.terminal E => k.toFun x) i.inv_hom_id }

/-- The chosen terminal object of `TS_E` has the full heap. -/
theorem TokenClass.terminal_heap_eq_univ : (⊤_ TokenClass.{u} E).heap = Set.univ := by
  let i : ⊤_ TokenClass.{u} E ≅ TokenClass.terminal E :=
    Limits.terminalIsTerminal.uniqueUpToIso TokenClass.terminalIsTerminal
  apply Set.eq_univ_of_forall
  intro w
  have h := i.inv.preserves (wordMap i.hom.toFun w) trivial
  rw [← Function.comp_apply (f := wordMap i.inv.toFun), ← wordMap_comp] at h
  have hid : i.inv.toFun ∘ i.hom.toFun = id := by
    funext x
    exact congrArg (fun k : ⊤_ TokenClass.{u} E ⟶ ⊤_ TokenClass.{u} E => k.toFun x) i.hom_inv_id
  rw [hid, wordMap_id, id_eq] at h
  exact h

/-- `⊤ : 1 → Ω` picks `1`. -/
noncomputable def TokenClass.truth : ⊤_ TokenClass.{u} E ⟶ TokenClass.omega E :=
  TokenClass.toOmega (fun _ => true)

theorem TokenClass.truth_isInduced : TokenClass.IsInduced (TokenClass.truth.{u} (E := E)) := by
  refine ⟨fun x y _ => ?_, ?_⟩
  · exact TokenClass.terminalCarrierEquiv.injective (Subsingleton.elim _ _)
  · rw [TokenClass.terminal_heap_eq_univ]
    exact (Set.eq_univ_of_forall fun _ => trivial).symm

/-- The characteristic map of an injective Token map. -/
noncomputable def TokenClass.charMap {TU TX : TokenClass.{u} E} (m : TU ⟶ TX) : TX ⟶ TokenClass.omega E := by
  classical
  exact TokenClass.toOmega (fun x => decide (∃ u, m.toFun u = x))

theorem TokenClass.charMap_apply {TU TX : TokenClass.{u} E} (m : TU ⟶ TX) (x : TX.carrier) :
    ((TokenClass.charMap m).toFun x).down = true ↔ ∃ u, m.toFun u = x := by
  simp [TokenClass.charMap, TokenClass.toOmega]

theorem TokenClass.truth_apply (t : (⊤_ TokenClass.{u} E).carrier) :
    (TokenClass.truth.toFun t).down = true := rfl

theorem TokenClass.charMap_cone_mem {TU TX : TokenClass.{u} E} (m : TU ⟶ TX)
    (s : PullbackCone (TokenClass.charMap m) TokenClass.truth) (x : s.pt.carrier) :
    ∃ u, m.toFun u = s.fst.toFun x := by
  rw [← TokenClass.charMap_apply]
  have := congrArg (fun k : s.pt ⟶ TokenClass.omega E => (k.toFun x).down) s.condition
  simpa [TokenClass.truth_apply] using this

/-- An induced embedding is the pullback of `⊤` along its characteristic map. -/
theorem TokenClass.isPullback_charMap {TU TX : TokenClass.{u} E} (m : TU ⟶ TX)
    (hm : TokenClass.IsInduced m) :
    IsPullback m (terminal.from TU) (TokenClass.charMap m) TokenClass.truth := by
  have hsq : m ≫ TokenClass.charMap m = terminal.from TU ≫ TokenClass.truth := by
    apply TokenClass.Hom.ext; funext u
    apply ULift.ext_iff.mpr
    simp only [comp_toFun, Function.comp_apply]
    rw [TokenClass.truth_apply, TokenClass.charMap_apply]
    exact ⟨u, rfl⟩
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hsq ?_ ?_ ?_ ?_)
  · intro s
    refine ⟨fun x => Classical.choose (TokenClass.charMap_cone_mem m s x), fun w hw => ?_⟩
    rw [hm.2, Set.mem_preimage, ← Function.comp_apply (f := wordMap m.toFun), ← wordMap_comp]
    have : m.toFun ∘ (fun x => Classical.choose (TokenClass.charMap_cone_mem m s x)) = s.fst.toFun :=
      funext fun x => Classical.choose_spec (TokenClass.charMap_cone_mem m s x)
    rw [this]; exact s.fst.preserves w hw
  · intro s
    apply TokenClass.Hom.ext; funext x
    exact Classical.choose_spec (TokenClass.charMap_cone_mem m s x)
  · intro s; exact terminal.hom_ext _ _
  · intro s k hk _
    apply TokenClass.Hom.ext; funext x
    apply hm.1
    have := congrArg (fun k : s.pt ⟶ TX => k.toFun x) hk
    simp only [comp_toFun, Function.comp_apply] at this
    rw [this]
    exact (Classical.choose_spec (TokenClass.charMap_cone_mem m s x)).symm

/-- `⊤ : T_1 → Ω` classifies strong subobjects in `TS_E`. -/
noncomputable def TokenClass.strongSubobjectClassifier : StrongSubobjectClassifier (TokenClass.{u} E) where
  Ω := TokenClass.omega E
  truth := TokenClass.truth
  truth_strongMono := (TokenClass.strongMono_iff_isInduced _).2 TokenClass.truth_isInduced
  classify := by
    classical
    intro TU TX m hm
    have hind := (TokenClass.strongMono_iff_isInduced m).1 hm
    refine ⟨TokenClass.charMap m, TokenClass.isPullback_charMap m hind, ?_⟩
    intro χ hχ
    apply TokenClass.Hom.ext; funext x
    apply ULift.ext_iff.mpr
    rw [TokenClass.charMap, TokenClass.toOmega]
    simp only
    by_cases hx : ∃ u, m.toFun u = x
    · obtain ⟨u, rfl⟩ := hx
      have := congrArg (fun k : TU ⟶ TokenClass.omega E => (k.toFun u).down) hχ.w
      simpa [TokenClass.truth_apply] using this
    · rw [decide_eq_false hx]
      by_contra hcon
      have htrue : (χ.toFun x).down = true := by
        cases h : (χ.toFun x).down
        · exact absurd h hcon
        · rfl
      have hw : TokenClass.ofPoint x ≫ χ = terminal.from (TokenClass.point E) ≫ TokenClass.truth := by
        apply TokenClass.Hom.ext; funext _
        exact ULift.ext_iff.mpr htrue
      have := congrArg (fun k : TokenClass.point E ⟶ TX => k.toFun PUnit.unit) (hχ.lift_fst _ _ hw)
      exact hx ⟨_, this⟩

/-- `TS_E` is an elementary quasitopos (the ambient statement; cf. Parker, Thm 4.5). -/
instance TokenClass.isQuasitopos : IsQuasitopos (TokenClass.{u} E) where
  locallyCartesianClosed := TokenClass.locallyCartesianClosed
  classifier := ⟨TokenClass.strongSubobjectClassifier⟩

/-! ### Theorem 5.5 for the regular fragment -/

theorem RegTS.mono_iff_injective [Finite E] {TA TB : RegTS.{u} E} (m : TA ⟶ TB) :
    Mono m ↔ Function.Injective m.hom.toFun := by
  constructor
  · intro hm a₁ a₂ h
    let P : RegTS.{u} E := ⟨TokenClass.point E, inferInstance, TokenClass.point_isRegular⟩
    have : (ObjectProperty.homMk (TokenClass.ofPoint a₁) : P ⟶ TA) ≫ m =
        ObjectProperty.homMk (TokenClass.ofPoint a₂) ≫ m :=
      InducedCategory.hom_ext (TokenClass.Hom.ext (funext fun _ => h))
    exact congrArg (fun k : P ⟶ TA => k.hom.toFun PUnit.unit) (hm.right_cancellation _ _ this)
  · intro hm
    refine ⟨fun g h hgh => InducedCategory.hom_ext (TokenClass.Hom.ext (funext fun x => hm ?_))⟩
    exact congrArg (fun k : _ ⟶ TB => k.hom.toFun x) hgh

theorem RegTS.epi_iff_surjective [Finite E] {TA TB : RegTS.{u} E} (m : TA ⟶ TB) :
    Epi m ↔ Function.Surjective m.hom.toFun := by
  classical
  constructor
  · intro hm b
    by_contra hb
    let Om : RegTS.{u} E := ⟨TokenClass.omega E, inferInstance, TokenClass.omega_isRegular⟩
    have h : m ≫ (ObjectProperty.homMk (TokenClass.toOmega (fun _ => true)) : TB ⟶ Om) =
        m ≫ ObjectProperty.homMk (TokenClass.toOmega (fun b' => decide (∃ a, m.hom.toFun a = b'))) :=
      InducedCategory.hom_ext (TokenClass.Hom.ext (funext fun a => by
        change (ULift.up true : ULift Bool) = ULift.up (decide (∃ a', m.hom.toFun a' = m.hom.toFun a))
        congr 1; symm; simp))
    have := congrArg (fun k : TB ⟶ Om => (k.hom.toFun b).down) (hm.left_cancellation _ _ h)
    simp [TokenClass.toOmega] at this
    exact hb this
  · intro hm
    refine ⟨fun g h hgh => InducedCategory.hom_ext (TokenClass.Hom.ext (funext fun b => ?_))⟩
    obtain ⟨a, rfl⟩ := hm b
    exact congrArg (fun k : TA ⟶ _ => k.hom.toFun a) hgh

theorem RegTS.strongMono_iff_isInduced [Finite E] {TA TB : RegTS.{u} E} (m : TA ⟶ TB) :
    StrongMono m ↔ TokenClass.IsInduced m.hom := by
  constructor
  · intro hm
    have := hm.mono
    refine ⟨(RegTS.mono_iff_injective m).1 inferInstance, ?_⟩
    have hAfin : Finite TA.obj.carrier := TA.property.1
    let TI : RegTS.{u} E := ⟨⟨TA.obj.carrier, wordMap m.hom.toFun ⁻¹' TB.obj.heap⟩, hAfin,
      Language.IsRegular.comap_wordMap m.hom.toFun TB.property.2⟩
    let u : TA ⟶ TI := ObjectProperty.homMk ⟨id, fun w hw => by
      show wordMap m.hom.toFun (wordMap id w) ∈ TB.obj.heap
      rw [wordMap_id]; exact m.hom.preserves w hw⟩
    let j : TI ⟶ TB := ObjectProperty.homMk ⟨m.hom.toFun, fun _ hw => hw⟩
    have : Epi u := (RegTS.epi_iff_surjective u).2 (fun a => ⟨a, rfl⟩)
    have sq : CommSq (𝟙 TA) u m j := ⟨InducedCategory.hom_ext (TokenClass.Hom.ext rfl)⟩
    have := hm.rlp u
    obtain ⟨⟨l, hl₁, _⟩⟩ := (HasLiftingProperty.sq_hasLift sq).exists_lift
    have hl : l.hom.toFun = id := by
      funext x; exact congrArg (fun k : TA ⟶ TA => k.hom.toFun x) hl₁
    apply Set.Subset.antisymm
    · intro w hw; exact m.hom.preserves w hw
    · intro w hw
      have := l.hom.preserves w hw
      rwa [hl, wordMap_id] at this
  · rintro ⟨hinj, hheap⟩
    have : Mono m := (RegTS.mono_iff_injective m).2 hinj
    refine ⟨inferInstance, fun X Y z hz => ⟨fun {uu} {v} sq => ?_⟩⟩
    have hz' := (RegTS.epi_iff_surjective z).1 hz
    have hsq := congrArg (fun k : X ⟶ TB => k.hom.toFun) sq.w
    simp only [ObjectProperty.FullSubcategory.comp_hom, TokenClass.comp_toFun] at hsq
    choose pre hpre using hz'
    have key : ∀ x, uu.hom.toFun x = uu.hom.toFun (pre (z.hom.toFun x)) := by
      intro x
      apply hinj
      have h1 := congrFun hsq x
      have h2 := congrFun hsq (pre (z.hom.toFun x))
      simp only [Function.comp_apply] at h1 h2
      rw [h1, h2, hpre]
    have hcomp : m.hom.toFun ∘ (fun y => uu.hom.toFun (pre y)) = v.hom.toFun := by
      funext y
      have := congrFun hsq (pre y)
      simp only [Function.comp_apply] at this
      rw [Function.comp_apply, this, hpre]
    let d : Y ⟶ TA := ObjectProperty.homMk ⟨fun y => uu.hom.toFun (pre y), fun w hw => by
      rw [hheap, Set.mem_preimage, ← Function.comp_apply (f := wordMap m.hom.toFun), ← wordMap_comp,
        hcomp]
      exact v.hom.preserves w hw⟩
    exact ⟨⟨⟨d, InducedCategory.hom_ext (TokenClass.Hom.ext (funext fun x => (key x).symm)),
      InducedCategory.hom_ext (TokenClass.Hom.ext (funext fun y => congrFun hcomp y))⟩⟩⟩

/-! ### Local cartesian closure of `RegTS_E` -/

section regLCC
variable [Finite E]

instance RegTS.finiteCarrier (T : RegTS.{u} E) : Finite T.obj.carrier := T.property.1

omit [Finite E] in
theorem TokenClass.finite_pb {TA TB TC : TokenClass.{u} E} (f : TA ⟶ TC) (g : TB ⟶ TC)
    [Finite TA.carrier] [Finite TB.carrier] : Finite (TokenClass.pb f g).carrier :=
  inferInstanceAs (Finite {x : TA.carrier × TB.carrier // f.toFun x.1 = g.toFun x.2})

omit [Finite E] in
theorem TokenClass.finite_depProd {TA TB TX : TokenClass.{u} E} (p : TA ⟶ TB) (q : TX ⟶ TA)
    [Finite TA.carrier] [Finite TB.carrier] [Finite TX.carrier] :
    Finite (TokenClass.depProd p q).carrier := by
  show Finite (TokenClass.depProdCarrier p q)
  unfold TokenClass.depProdCarrier TokenClass.sectionsOver
  infer_instance

/-- The pullback `T_A ×_{T_C} T_B` in `RegTS_E`. -/
def RegTS.pb {TA TB TC : RegTS.{u} E} (f : TA ⟶ TC) (g : TB ⟶ TC) : RegTS.{u} E :=
  ⟨TokenClass.pb f.hom g.hom, TokenClass.finite_pb f.hom g.hom,
    TokenClass.pb_isRegular f.hom g.hom TA.property.2 TB.property.2⟩

/-- The dependent product `Π_p(q)` in `RegTS_E`. -/
def RegTS.depProd {TA TB TX : RegTS.{u} E} (p : TA ⟶ TB) (q : TX ⟶ TA) : RegTS.{u} E :=
  ⟨TokenClass.depProd p.hom q.hom, TokenClass.finite_depProd p.hom q.hom,
    TokenClass.depProd_isRegular p.hom q.hom TA.property.2 TB.property.2 TX.property.2⟩

/-- The underlying `TS_E`-slice object of a `RegTS_E`-slice object. -/
abbrev RegTS.overObj {X : RegTS.{u} E} (Z : Over X) : Over X.obj := Over.mk Z.hom.hom

section regPullback
variable {TY TX : RegTS.{u} E} (g : TY ⟶ TX)

/-- Pullback along `g : T_Y ⟶ T_X` as a functor `Over T_X ⥤ Over T_Y` in `RegTS_E`. -/
def RegTS.pullbackF : Over TX ⥤ Over TY where
  obj Z := Over.mk (X := TY) (Y := RegTS.pb Z.hom g)
    (ObjectProperty.homMk (TokenClass.pbSnd Z.hom.hom g.hom))
  map {Z Z'} k := Over.homMk (ObjectProperty.homMk
    (TokenClass.pbLift Z'.hom.hom g.hom (TokenClass.pbFst Z.hom.hom g.hom ≫ k.left.hom)
      (TokenClass.pbSnd Z.hom.hom g.hom)
      (TokenClass.Hom.ext (funext fun x =>
        (congrArg (fun m : Z.left ⟶ TX => m.hom.toFun x.1.1) (Over.w k)).trans x.2))))
    (InducedCategory.hom_ext (TokenClass.Hom.ext rfl))
  map_id _ := Over.OverMorphism.ext (InducedCategory.hom_ext (TokenClass.Hom.ext rfl))
  map_comp _ _ := Over.OverMorphism.ext (InducedCategory.hom_ext (TokenClass.Hom.ext rfl))

/-- `Σ_g ⊣ g^*` in `RegTS_E`. -/
def RegTS.mapPullbackAdj : Over.map g ⊣ RegTS.pullbackF g :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun W Z =>
        { toFun := fun k => Over.homMk (ObjectProperty.homMk
            (TokenClass.pbLift Z.hom.hom g.hom k.left.hom W.hom.hom
              (congrArg InducedCategory.Hom.hom (Over.w k))))
            (InducedCategory.hom_ext (TokenClass.Hom.ext rfl))
          invFun := fun m => Over.homMk
            (ObjectProperty.homMk (m.left.hom ≫ TokenClass.pbFst Z.hom.hom g.hom))
            (InducedCategory.hom_ext (TokenClass.Hom.ext (funext fun w =>
              (m.left.hom.toFun w).2.trans
                (congrArg (fun k : W.left ⟶ TY => g.hom.toFun (k.hom.toFun w)) (Over.w m)))))
          left_inv := fun _ => Over.OverMorphism.ext (InducedCategory.hom_ext (TokenClass.Hom.ext rfl))
          right_inv := fun m => Over.OverMorphism.ext (InducedCategory.hom_ext (TokenClass.Hom.ext
            (funext fun w => Subtype.ext (Prod.ext rfl
              (congrArg (fun k : W.left ⟶ TY => k.hom.toFun w) (Over.w m)).symm)))) }
      homEquiv_naturality_left_symm := fun _ _ =>
        Over.OverMorphism.ext (InducedCategory.hom_ext (TokenClass.Hom.ext rfl))
      homEquiv_naturality_right := fun _ _ =>
        Over.OverMorphism.ext (InducedCategory.hom_ext (TokenClass.Hom.ext rfl)) }

end regPullback

section regPushforward
variable {TA TB : RegTS.{u} E} (p : TA ⟶ TB)

/-- The dependent-product functor `Π_p : Over T_A ⥤ Over T_B` in `RegTS_E`. -/
def RegTS.pushforward : Over TA ⥤ Over TB where
  obj q := Over.mk (X := TB) (Y := RegTS.depProd p q.hom)
    (ObjectProperty.homMk (TokenClass.depProdHom p.hom q.hom.hom))
  map k := Over.homMk (ObjectProperty.homMk
    ⟨TokenClass.depProdMapFun p.hom k.left.hom (congrArg InducedCategory.Hom.hom (Over.w k)),
      TokenClass.depProdMapFun_preserves p.hom k.left.hom
        (congrArg InducedCategory.Hom.hom (Over.w k))⟩)
    (InducedCategory.hom_ext (TokenClass.Hom.ext rfl))
  map_id _ := Over.OverMorphism.ext (InducedCategory.hom_ext (TokenClass.Hom.ext rfl))
  map_comp _ _ := Over.OverMorphism.ext (InducedCategory.hom_ext (TokenClass.Hom.ext rfl))

/-- The adjunction `p^* ⊣ Π_p` in `RegTS_E`. -/
def RegTS.pullbackPushforwardAdj : RegTS.pullbackF p ⊣ RegTS.pushforward p :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun Z q =>
        { toFun := fun g => Over.homMk (ObjectProperty.homMk
            ⟨TokenClass.curryFun p.hom (RegTS.overObj Z) q.hom.hom g.left.hom
                (congrArg InducedCategory.Hom.hom (Over.w g)),
              TokenClass.curryFun_preserves p.hom (RegTS.overObj Z) q.hom.hom g.left.hom
                (congrArg InducedCategory.Hom.hom (Over.w g))⟩)
            (InducedCategory.hom_ext (TokenClass.Hom.ext rfl))
          invFun := fun h => Over.homMk (ObjectProperty.homMk
            ⟨TokenClass.uncurryFun p.hom (RegTS.overObj Z) q.hom.hom h.left.hom
                (congrArg InducedCategory.Hom.hom (Over.w h)),
              TokenClass.uncurryFun_preserves p.hom (RegTS.overObj Z) q.hom.hom h.left.hom
                (congrArg InducedCategory.Hom.hom (Over.w h))⟩)
            (InducedCategory.hom_ext (TokenClass.Hom.ext
              (funext fun x => (h.left.hom.toFun x.1.1).2.2 _)))
          left_inv := fun _ => Over.OverMorphism.ext (InducedCategory.hom_ext (TokenClass.Hom.ext rfl))
          right_inv := fun h => Over.OverMorphism.ext (InducedCategory.hom_ext (TokenClass.Hom.ext
            (funext fun z => TokenClass.depProd_ext p.hom
              (congrArg (fun m : Z.left ⟶ TB => m.hom.toFun z) (Over.w h)).symm
              (fun _ _ _ => rfl)))) }
      homEquiv_naturality_left_symm := fun _ _ =>
        Over.OverMorphism.ext (InducedCategory.hom_ext (TokenClass.Hom.ext rfl))
      homEquiv_naturality_right := fun _ _ =>
        Over.OverMorphism.ext (InducedCategory.hom_ext (TokenClass.Hom.ext rfl)) }

end regPushforward

section regSlice
variable {TX : RegTS.{u} E}

/-- The binary fan `Y ×_X Z := Σ_{Y}(Y^* Z)` in `Over T_X` for `RegTS_E`. -/
abbrev RegTS.overFan (Y Z : Over TX) : BinaryFan Y Z :=
  BinaryFan.mk (P := (Over.map Y.hom).obj ((RegTS.pullbackF Y.hom).obj Z))
    (Over.homMk (ObjectProperty.homMk (TokenClass.pbSnd Z.hom.hom Y.hom.hom))
      (InducedCategory.hom_ext (TokenClass.Hom.ext rfl)))
    (Over.homMk (ObjectProperty.homMk (TokenClass.pbFst Z.hom.hom Y.hom.hom))
      (InducedCategory.hom_ext (TokenClass.pb_condition Z.hom.hom Y.hom.hom)))

def RegTS.overFanIsLimit (Y Z : Over TX) : IsLimit (RegTS.overFan Y Z) :=
  BinaryFan.IsLimit.mk _
    (fun {W} u v => Over.homMk
      (ObjectProperty.homMk (TokenClass.pbLift Z.hom.hom Y.hom.hom v.left.hom u.left.hom
        ((congrArg InducedCategory.Hom.hom (Over.w v)).trans
          (congrArg InducedCategory.Hom.hom (Over.w u)).symm)))
      (InducedCategory.hom_ext (TokenClass.Hom.ext (funext fun w =>
        congrArg (fun m : W.left ⟶ TX => m.hom.toFun w) (Over.w u)))))
    (fun _ _ => Over.OverMorphism.ext (InducedCategory.hom_ext (TokenClass.Hom.ext rfl)))
    (fun _ _ => Over.OverMorphism.ext (InducedCategory.hom_ext (TokenClass.Hom.ext rfl)))
    (fun _ _ _ h1 h2 => Over.OverMorphism.ext (InducedCategory.hom_ext (TokenClass.Hom.ext
      (funext fun w => Subtype.ext (Prod.ext
        (congrArg (fun k : _ ⟶ Z => k.left.hom.toFun w) h2)
        (congrArg (fun k : _ ⟶ Y => k.left.hom.toFun w) h1))))))

/-- The cartesian monoidal structure on `Over T_X` in `RegTS_E`. -/
@[instance_reducible]
def RegTS.overCMC (TX : RegTS.{u} E) : CartesianMonoidalCategory (Over TX) :=
  CartesianMonoidalCategory.ofChosenFiniteProducts
    ⟨Limits.asEmptyCone (Over.mk (𝟙 TX)),
      Limits.IsTerminal.ofUniqueHom (fun Y => Over.homMk Y.hom)
        fun Y m => Over.OverMorphism.ext (by simpa using m.w)⟩
    (fun Y Z => ⟨_, RegTS.overFanIsLimit Y Z⟩)

attribute [local instance] RegTS.overCMC

open MonoidalCategory in
/-- `Y ⊗ -` is `Σ_Y ∘ Y^*` on the nose. -/
def RegTS.tensorLeftIso (Y : Over TX) :
    RegTS.pullbackF Y.hom ⋙ Over.map Y.hom ≅ tensorLeft Y :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => Over.OverMorphism.ext (InducedCategory.hom_ext (TokenClass.Hom.ext rfl)))

open MonoidalCategory in
instance RegTS.overClosed (Y : Over TX) : Closed Y where
  rightAdj := RegTS.pullbackF Y.hom ⋙ RegTS.pushforward Y.hom
  adj := ((RegTS.pullbackPushforwardAdj Y.hom).comp (RegTS.mapPullbackAdj Y.hom)).ofNatIsoLeft
    (RegTS.tensorLeftIso Y)

instance RegTS.overMonoidalClosed (TX : RegTS.{u} E) : MonoidalClosed (Over TX) where

end regSlice

/-- `RegTS_E` is locally cartesian closed. -/
theorem RegTS.locallyCartesianClosed (X : RegTS.{u} E) :
    ∃ _ : CartesianMonoidalCategory (Over X), Nonempty (MonoidalClosed (Over X)) :=
  ⟨RegTS.overCMC X, ⟨RegTS.overMonoidalClosed X⟩⟩

end regLCC

/-! ### The strong-subobject classifier of `RegTS_E` -/

section regClassifier

/-- Any terminal object of `TS_E` has a subsingleton carrier. -/
theorem TokenClass.subsingleton_of_isTerminal {T : TokenClass.{u} E} (hT : IsTerminal T) :
    Subsingleton T.carrier :=
  ⟨fun x y => congrArg (fun k : TokenClass.point E ⟶ T => k.toFun PUnit.unit)
    (hT.hom_ext (TokenClass.ofPoint x) (TokenClass.ofPoint y))⟩

/-- Any terminal object of `TS_E` has the full heap. -/
theorem TokenClass.heap_eq_univ_of_isTerminal {T : TokenClass.{u} E} (hT : IsTerminal T) :
    T.heap = Set.univ := by
  let i : T ≅ TokenClass.terminal E := hT.uniqueUpToIso TokenClass.terminalIsTerminal
  apply Set.eq_univ_of_forall
  intro w
  have h := i.inv.preserves (wordMap i.hom.toFun w) trivial
  rw [← Function.comp_apply (f := wordMap i.inv.toFun), ← wordMap_comp] at h
  have hid : i.inv.toFun ∘ i.hom.toFun = id := by
    funext x
    exact congrArg (fun k : T ⟶ T => k.toFun x) i.hom_inv_id
  rw [hid, wordMap_id, id_eq] at h
  exact h

/-- `⊤ : T → Ω` for an arbitrary (terminal) `T`. -/
def TokenClass.truthFrom (T : TokenClass.{u} E) : T ⟶ TokenClass.omega E :=
  TokenClass.toOmega (fun _ => true)

theorem TokenClass.truthFrom_isInduced {T : TokenClass.{u} E} (hT : IsTerminal T) :
    TokenClass.IsInduced (TokenClass.truthFrom T) := by
  refine ⟨fun x y _ => ?_, ?_⟩
  · have := TokenClass.subsingleton_of_isTerminal hT
    exact Subsingleton.elim _ _
  · rw [TokenClass.heap_eq_univ_of_isTerminal hT]
    exact (Set.eq_univ_of_forall fun _ => trivial).symm

theorem TokenClass.truthFrom_apply {T : TokenClass.{u} E} (t : T.carrier) :
    ((TokenClass.truthFrom T).toFun t).down = true := rfl

theorem TokenClass.charMap_cone_mem' {TU TX T : TokenClass.{u} E} (m : TU ⟶ TX)
    (s : PullbackCone (TokenClass.charMap m) (TokenClass.truthFrom T)) (x : s.pt.carrier) :
    ∃ u, m.toFun u = s.fst.toFun x := by
  rw [← TokenClass.charMap_apply]
  have := congrArg (fun k : s.pt ⟶ TokenClass.omega E => (k.toFun x).down) s.condition
  simpa [TokenClass.truthFrom_apply] using this

/-- An induced embedding is the pullback of `⊤ : T → Ω` along its characteristic map, for any
terminal `T` and any `t : T_U → T`. -/
theorem TokenClass.isPullback_charMap' {TU TX T : TokenClass.{u} E} (hT : IsTerminal T)
    (m : TU ⟶ TX) (hm : TokenClass.IsInduced m) (t : TU ⟶ T) :
    IsPullback m t (TokenClass.charMap m) (TokenClass.truthFrom T) := by
  have hsq : m ≫ TokenClass.charMap m = t ≫ TokenClass.truthFrom T := by
    apply TokenClass.Hom.ext; funext u
    apply ULift.ext_iff.mpr
    simp only [comp_toFun, Function.comp_apply]
    show _ = true
    rw [TokenClass.charMap_apply]
    exact ⟨u, rfl⟩
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hsq ?_ ?_ ?_ ?_)
  · intro s
    refine ⟨fun x => Classical.choose (TokenClass.charMap_cone_mem' m s x), fun w hw => ?_⟩
    rw [hm.2, Set.mem_preimage, ← Function.comp_apply (f := wordMap m.toFun), ← wordMap_comp]
    have : m.toFun ∘ (fun x => Classical.choose (TokenClass.charMap_cone_mem' m s x)) = s.fst.toFun :=
      funext fun x => Classical.choose_spec (TokenClass.charMap_cone_mem' m s x)
    rw [this]; exact s.fst.preserves w hw
  · intro s
    apply TokenClass.Hom.ext; funext x
    exact Classical.choose_spec (TokenClass.charMap_cone_mem' m s x)
  · intro s; exact hT.hom_ext _ _
  · intro s k hk _
    apply TokenClass.Hom.ext; funext x
    apply hm.1
    have := congrArg (fun k : s.pt ⟶ TX => k.toFun x) hk
    simp only [comp_toFun, Function.comp_apply] at this
    rw [this]
    exact (Classical.choose_spec (TokenClass.charMap_cone_mem' m s x)).symm

variable [Finite E]

instance RegTS.instHasFiniteLimits : HasFiniteLimits (RegTS.{u} E) := RegTS.hasFiniteLimits
instance RegTS.instHasFiniteColimits : HasFiniteColimits (RegTS.{u} E) := RegTS.hasFiniteColimits

/-- `Ω` as an object of `RegTS_E`. -/
def RegTS.omega : RegTS.{u} E := ⟨TokenClass.omega E, inferInstance, TokenClass.omega_isRegular⟩

/-- The one-point token class with full heap, as an object of `RegTS_E`. -/
def RegTS.pt : RegTS.{u} E :=
  ⟨TokenClass.terminal E, inferInstanceAs (Finite PUnit), TokenClass.terminal_isRegular⟩

def RegTS.ptIsTerminal : IsTerminal (RegTS.pt.{u} (E := E)) :=
  IsTerminal.ofUniqueHom (fun _ => ObjectProperty.homMk ⟨fun _ => PUnit.unit, fun _ _ => trivial⟩)
    (fun _ _ => InducedCategory.hom_ext (TokenClass.Hom.ext (funext fun _ => rfl)))

/-- The terminal object of `RegTS_E` is terminal in `TS_E`. -/
noncomputable def RegTS.terminalObjIsTerminal : IsTerminal (⊤_ RegTS.{u} E).obj :=
  IsTerminal.ofIso TokenClass.terminalIsTerminal
    ((isRegTS.{u} E).ι.mapIso (Limits.terminalIsTerminal.uniqueUpToIso RegTS.ptIsTerminal)).symm

/-- `⊤ : 1 → Ω` in `RegTS_E`. -/
noncomputable def RegTS.truth : ⊤_ RegTS.{u} E ⟶ RegTS.omega :=
  ObjectProperty.homMk (TokenClass.truthFrom _)

/-- `⊤ : 1 → Ω` classifies strong subobjects in `RegTS_E`. -/
noncomputable def RegTS.strongSubobjectClassifier : StrongSubobjectClassifier (RegTS.{u} E) where
  Ω := RegTS.omega
  truth := RegTS.truth
  truth_strongMono := (RegTS.strongMono_iff_isInduced _).2
    (TokenClass.truthFrom_isInduced RegTS.terminalObjIsTerminal)
  classify := by
    classical
    intro TU TX m hm
    have hind := (RegTS.strongMono_iff_isInduced m).1 hm
    refine ⟨ObjectProperty.homMk (TokenClass.charMap m.hom), ?_, ?_⟩
    · exact IsPullback.of_map_of_faithful (isRegTS.{u} E).ι
        (TokenClass.isPullback_charMap' RegTS.terminalObjIsTerminal m.hom hind _)
    intro χ hχ
    apply InducedCategory.hom_ext
    apply TokenClass.Hom.ext; funext x
    apply ULift.ext_iff.mpr
    show _ = ((TokenClass.charMap m.hom).toFun x).down
    rw [TokenClass.charMap, TokenClass.toOmega]
    simp only
    by_cases hx : ∃ u, m.hom.toFun u = x
    · obtain ⟨u, rfl⟩ := hx
      have := congrArg (fun k : TU ⟶ RegTS.omega => (k.hom.toFun u).down) hχ.w
      rw [decide_eq_true ⟨u, rfl⟩]
      exact this
    · rw [decide_eq_false hx]
      by_contra hcon
      have htrue : (χ.hom.toFun x).down = true := by
        cases h : (χ.hom.toFun x).down
        · exact absurd h hcon
        · rfl
      let P : RegTS.{u} E := ⟨TokenClass.point E, inferInstance, TokenClass.point_isRegular⟩
      have hw : (ObjectProperty.homMk (TokenClass.ofPoint x) : P ⟶ TX) ≫ χ =
          terminal.from P ≫ RegTS.truth := by
        apply InducedCategory.hom_ext
        apply TokenClass.Hom.ext; funext _
        exact ULift.ext_iff.mpr htrue
      have := congrArg (fun k : P ⟶ TX => k.hom.toFun PUnit.unit) (hχ.lift_fst _ _ hw)
      exact hx ⟨_, this⟩

end regClassifier

/-- **Theorem 5.5** (effective quasitopos structure): `RegTS_E` is an elementary quasitopos. -/
theorem RegTS.isQuasitopos [Finite E] : Nonempty (IsQuasitopos (RegTS.{u} E)) :=
  ⟨{ locallyCartesianClosed := RegTS.locallyCartesianClosed
     classifier := ⟨RegTS.strongSubobjectClassifier⟩ }⟩

/-- **Main theorem** (restated): for every finite core, finite carriers with regular heaps
form an elementary quasitopos. -/
theorem mainTheorem (E : Type v) [Finite E] : Nonempty (IsQuasitopos (RegTS.{u} E)) :=
  RegTS.isQuasitopos

/-! ### Remark 5.6 -/

/-- **Remark 5.6** (part): the base condition in (5.6) is essential. With `A = X = ∅`,
`B = {*}`, all heaps empty, `S` is a singleton with no failures; omitting the base condition
would give `S` the full heap, and `r` would not be a Token map. -/
theorem base_condition_essential :
    let TA : TokenClass.{0} Unit := ⟨PEmpty, ∅⟩
    let TB : TokenClass.{0} Unit := ⟨PUnit, ∅⟩
    let p : TA ⟶ TB := ⟨fun x => x.elim, fun _ hw => hw.elim⟩
    let q : TA ⟶ TA := 𝟙 TA
    TokenClass.depProdFailures p q = ∅ ∧
    ¬ ∀ w : Word (TokenClass.depProdCarrier p q) Unit, wordMap (TokenClass.depProdBase p q) w ∈ TB.heap := by
  intro TA TB p q
  refine ⟨?_, ?_⟩
  · apply Set.eq_empty_of_forall_notMem
    rintro w ⟨hA, -⟩
    exact hA
  · intro h
    exact h []

/-- **Remark 5.6** (part): the identity carrier map from a singleton with empty heap to a
singleton with full heap is monic and epic but not an isomorphism; hence `RegTS_E` is not
balanced and not a topos. -/
theorem RegTS.not_balanced (E : Type v) [Finite E] :
    ∃ (TA TB : RegTS.{u} E) (m : TA ⟶ TB), Mono m ∧ Epi m ∧ ¬ IsIso m := by
  refine ⟨⟨TokenClass.point E, inferInstance, TokenClass.point_isRegular⟩,
    ⟨TokenClass.terminal E, inferInstance, TokenClass.terminal_isRegular⟩,
    ObjectProperty.homMk ⟨fun _ => PUnit.unit, fun _ _ => trivial⟩, ?_, ?_, ?_⟩
  · exact (RegTS.mono_iff_injective _).2 (fun x y _ => Subsingleton.elim (α := PUnit) x y)
  · exact (RegTS.epi_iff_surjective _).2 (fun y => ⟨PUnit.unit, rfl⟩)
  · intro h
    have hinv := h.out.choose_spec.2
    have := hinv.symm ▸ (h.out.choose.hom.preserves [Sum.inl PUnit.unit] trivial)
    exact this

end AT

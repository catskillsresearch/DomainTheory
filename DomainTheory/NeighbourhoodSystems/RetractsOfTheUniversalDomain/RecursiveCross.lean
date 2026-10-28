module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition_7_1

@[expose] public section

namespace Domain.Recursive

def consStep2 (w : ℕ) : ℕ := Nat.pair w.unpair.1 w.unpair.2.unpair.1 + 1

def appendCode (c1 c2 : ℕ) : ℕ := foldCode consStep2 0 c2 c1

def crossInnerStep (bop : ℕ → ℕ) (w : ℕ) : ℕ :=
  Nat.pair (bop (Nat.pair w.unpair.2.unpair.2 w.unpair.1)) w.unpair.2.unpair.1 + 1

def crossInner (bop : ℕ → ℕ) (x c2 : ℕ) : ℕ := foldCode (crossInnerStep bop) x 0 c2

def crossOuterStep (bop : ℕ → ℕ) (w : ℕ) : ℕ :=
  appendCode (crossInner bop w.unpair.1 w.unpair.2.unpair.2) w.unpair.2.unpair.1

def crossCombine (bop : ℕ → ℕ) (c1 c2 : ℕ) : ℕ := foldCode (crossOuterStep bop) c2 0 c1

def flatMapStep (f : ℕ → ℕ) (w : ℕ) : ℕ :=
  appendCode (f (Nat.pair w.unpair.2.unpair.2 w.unpair.1)) w.unpair.2.unpair.1

def flatMapCode (f : ℕ → ℕ) (x c : ℕ) : ℕ := foldCode (flatMapStep f) x 0 c

theorem consStep2_eq (x acc params : ℕ) :
    consStep2 (Nat.pair x (Nat.pair acc params)) = Nat.pair x acc + 1 := by
  unfold consStep2; simp only [unpair_pair_fst, unpair_pair_snd]

theorem mem_decodeList_appendCode_aux :
    ∀ (l : List ℕ) (acc z : ℕ),
      z ∈ decodeList (List.foldl (fun acc x => consStep2 (Nat.pair x (Nat.pair acc 0))) acc l)
        ↔ z ∈ l ∨ z ∈ decodeList acc
  | [], acc, z => by simp
  | a :: l, acc, z => by
    rw [List.foldl_cons, consStep2_eq, mem_decodeList_appendCode_aux l (Nat.pair a acc + 1) z,
      decodeList_succ, unpair_pair_fst, unpair_pair_snd]
    simp only [List.mem_cons]
    constructor
    · rintro (hl | (rfl | hacc))
      · exact Or.inl (Or.inr hl)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr hacc
    · rintro ((rfl | hl) | hacc)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl hl
      · exact Or.inr (Or.inr hacc)

theorem mem_decodeList_appendCode (c1 c2 z : ℕ) :
    z ∈ decodeList (appendCode c1 c2) ↔ z ∈ decodeList c1 ∨ z ∈ decodeList c2 := by
  unfold appendCode
  rw [foldCode_eq', mem_decodeList_appendCode_aux (decodeList c1) c2 z]

theorem crossInnerStep_eq (bop : ℕ → ℕ) (y acc x : ℕ) :
    crossInnerStep bop (Nat.pair y (Nat.pair acc x)) = Nat.pair (bop (Nat.pair x y)) acc + 1 := by
  unfold crossInnerStep; simp only [unpair_pair_fst, unpair_pair_snd]

private theorem mem_decodeList_crossInner_aux (bop : ℕ → ℕ) (x : ℕ) :
    ∀ (l : List ℕ) (acc z : ℕ),
      z ∈ decodeList
          (List.foldl (fun acc y => crossInnerStep bop (Nat.pair y (Nat.pair acc x))) acc l)
        ↔ (∃ y ∈ l, z = bop (Nat.pair x y)) ∨ z ∈ decodeList acc
  | [], acc, z => by simp
  | a :: l, acc, z => by
    rw [List.foldl_cons, crossInnerStep_eq,
      mem_decodeList_crossInner_aux bop x l (Nat.pair (bop (Nat.pair x a)) acc + 1) z,
      decodeList_succ, unpair_pair_fst, unpair_pair_snd]
    simp only [List.mem_cons]
    constructor
    · rintro (⟨y, hy, heq⟩ | (rfl | hacc))
      · exact Or.inl ⟨y, Or.inr hy, heq⟩
      · exact Or.inl ⟨a, Or.inl rfl, rfl⟩
      · exact Or.inr hacc
    · rintro (⟨y, (rfl | hy), heq⟩ | hacc)
      · exact Or.inr (Or.inl heq)
      · exact Or.inl ⟨y, hy, heq⟩
      · exact Or.inr (Or.inr hacc)

theorem mem_decodeList_crossInner {bop : ℕ → ℕ} (x c2 z : ℕ) :
    z ∈ decodeList (crossInner bop x c2) ↔ ∃ y ∈ decodeList c2, z = bop (Nat.pair x y) := by
  unfold crossInner
  rw [foldCode_eq', mem_decodeList_crossInner_aux bop x (decodeList c2) 0 z]
  simp only [decodeList_zero, List.not_mem_nil, or_false]

theorem crossOuterStep_eq (bop : ℕ → ℕ) (x acc c2 : ℕ) :
    crossOuterStep bop (Nat.pair x (Nat.pair acc c2)) = appendCode (crossInner bop x c2) acc := by
  unfold crossOuterStep; simp only [unpair_pair_fst, unpair_pair_snd]

theorem mem_decodeList_crossCombine_aux (bop : ℕ → ℕ) (c2 : ℕ) :
    ∀ (l : List ℕ) (acc z : ℕ),
      z ∈ decodeList (List.foldl (fun acc x => crossOuterStep bop (Nat.pair x (Nat.pair acc c2)))
          acc l)
        ↔ (∃ x ∈ l, ∃ y ∈ decodeList c2, z = bop (Nat.pair x y)) ∨ z ∈ decodeList acc
  | [], acc, z => by simp
  | a :: l, acc, z => by
    rw [List.foldl_cons, crossOuterStep_eq,
      mem_decodeList_crossCombine_aux bop c2 l (appendCode (crossInner bop a c2) acc) z,
      mem_decodeList_appendCode, mem_decodeList_crossInner]
    simp only [List.mem_cons]
    constructor
    · rintro (⟨x, hx, y, hy, heq⟩ | (⟨y, hy, heq⟩ | hacc))
      · exact Or.inl ⟨x, Or.inr hx, y, hy, heq⟩
      · exact Or.inl ⟨a, Or.inl rfl, y, hy, heq⟩
      · exact Or.inr hacc
    · rintro (⟨x, (rfl | hx), y, hy, heq⟩ | hacc)
      · exact Or.inr (Or.inl ⟨y, hy, heq⟩)
      · exact Or.inl ⟨x, hx, y, hy, heq⟩
      · exact Or.inr (Or.inr hacc)

theorem flatMapStep_eq (f : ℕ → ℕ) (y acc x : ℕ) :
    flatMapStep f (Nat.pair y (Nat.pair acc x)) = appendCode (f (Nat.pair x y)) acc := by
  unfold flatMapStep; simp only [unpair_pair_fst, unpair_pair_snd]

theorem mem_decodeList_flatMapCode_aux (f : ℕ → ℕ) (x : ℕ) :
    ∀ (l : List ℕ) (acc z : ℕ),
      z ∈ decodeList (List.foldl (fun acc y => flatMapStep f (Nat.pair y (Nat.pair acc x))) acc l)
        ↔ (∃ y ∈ l, z ∈ decodeList (f (Nat.pair x y))) ∨ z ∈ decodeList acc
  | [], acc, z => by simp
  | a :: l, acc, z => by
    rw [List.foldl_cons, flatMapStep_eq,
      mem_decodeList_flatMapCode_aux f x l (appendCode (f (Nat.pair x a)) acc) z,
      mem_decodeList_appendCode]
    simp only [List.mem_cons]
    constructor
    · rintro (⟨y, hy, hz⟩ | (hfa | hacc))
      · exact Or.inl ⟨y, Or.inr hy, hz⟩
      · exact Or.inl ⟨a, Or.inl rfl, hfa⟩
      · exact Or.inr hacc
    · rintro (⟨y, (rfl | hy), hz⟩ | hacc)
      · exact Or.inr (Or.inl hz)
      · exact Or.inl ⟨y, hy, hz⟩
      · exact Or.inr (Or.inr hacc)

theorem mem_decodeList_crossCombine {bop : ℕ → ℕ} (c1 c2 z : ℕ) :
    z ∈ decodeList (crossCombine bop c1 c2) ↔
      ∃ x ∈ decodeList c1, ∃ y ∈ decodeList c2, z = bop (Nat.pair x y) := by
  unfold crossCombine
  rw [foldCode_eq', mem_decodeList_crossCombine_aux bop c2 (decodeList c1) 0 z]
  simp only [decodeList_zero, List.not_mem_nil, or_false]

theorem mem_decodeList_flatMapCode {f : ℕ → ℕ} (x c z : ℕ) :
    z ∈ decodeList (flatMapCode f x c) ↔ ∃ y ∈ decodeList c, z ∈ decodeList (f (Nat.pair x y)) := by
  unfold flatMapCode
  rw [foldCode_eq', mem_decodeList_flatMapCode_aux f x (decodeList c) 0 z]
  simp only [decodeList_zero, List.not_mem_nil, or_false]

theorem primrec_consStep2 : Nat.Primrec consStep2 := by
  have h1 : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have h21 : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  exact (Nat.Primrec.succ.comp (h1.pair h21)).of_eq fun _ => rfl

theorem primrec_appendCode : Nat.Primrec (fun t => appendCode t.unpair.1 t.unpair.2) :=
  (primrec_foldCode primrec_consStep2 (Nat.Primrec.const 0) Nat.Primrec.right
    Nat.Primrec.left).of_eq fun _ => rfl

theorem primrec_crossInnerStep {bop : ℕ → ℕ} (hbop : Nat.Primrec bop) :
    Nat.Primrec (crossInnerStep bop) := by
  have hy : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  exact (Nat.Primrec.succ.comp ((hbop.comp (hx.pair hy)).pair hacc)).of_eq fun _ => rfl

theorem primrec_crossInner {bop : ℕ → ℕ} (hbop : Nat.Primrec bop) :
    Nat.Primrec (fun t => crossInner bop t.unpair.1 t.unpair.2) :=
  (primrec_foldCode (primrec_crossInnerStep hbop) Nat.Primrec.left (Nat.Primrec.const 0)
    Nat.Primrec.right).of_eq fun _ => rfl

theorem primrec_crossOuterStep {bop : ℕ → ℕ} (hbop : Nat.Primrec bop) :
    Nat.Primrec (crossOuterStep bop) := by
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hc2 : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hinner : Nat.Primrec (fun w : ℕ => crossInner bop w.unpair.1 w.unpair.2.unpair.2) :=
    ((primrec_crossInner hbop).comp (hx.pair hc2)).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_appendCode.comp (hinner.pair hacc)).of_eq fun w => by
    unfold crossOuterStep
    simp only [unpair_pair_fst, unpair_pair_snd]

theorem primrec_crossCombine {bop : ℕ → ℕ} (hbop : Nat.Primrec bop) :
    Nat.Primrec (fun t => crossCombine bop t.unpair.1 t.unpair.2) :=
  (primrec_foldCode (primrec_crossOuterStep hbop) Nat.Primrec.right (Nat.Primrec.const 0)
    Nat.Primrec.left).of_eq fun _ => rfl

theorem primrec_flatMapStep {f : ℕ → ℕ} (hf : Nat.Primrec f) : Nat.Primrec (flatMapStep f) := by
  have hy : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  exact (primrec_appendCode.comp ((hf.comp (hx.pair hy)).pair hacc)).of_eq fun w => by
    unfold flatMapStep; simp only [unpair_pair_fst, unpair_pair_snd]

theorem primrec_flatMapCode {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    Nat.Primrec (fun t => flatMapCode f t.unpair.1 t.unpair.2) :=
  (primrec_foldCode (primrec_flatMapStep hf) Nat.Primrec.left (Nat.Primrec.const 0)
    Nat.Primrec.right).of_eq fun _ => rfl

end Domain.Recursive

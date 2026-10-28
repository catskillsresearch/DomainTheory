module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_11
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_19
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_2
public import Mathlib.Data.Nat.Bits
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_16
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_7

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise516
section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

abbrev flip (σ : Str) : Str := σ.map not

@[simp] theorem flip_nil : flip [] = [] := rfl

@[simp] theorem flip_cons (b : Bool) (σ : Str) : flip (b :: σ) = (!b) :: flip σ := rfl

@[simp] theorem flip_flip (σ : Str) : flip (flip σ) = σ := by
  induction σ with
  | nil => rfl
  | cons b σ ih => simp [ih]

def double : Str → Str
  | [] => []
  | b :: σ => b :: b :: double σ

@[simp] theorem double_nil : double [] = [] := rfl

@[simp] theorem double_cons (b : Bool) (σ : Str) : double (b :: σ) = b :: b :: double σ := rfl

theorem double_append (σ τ : Str) : double (σ ++ τ) = double σ ++ double τ := by
  induction σ with
  | nil => rfl
  | cons b σ ih => simp [double, ih]

theorem double_prefix {σ τ : Str} (h : σ <+: τ) : double σ <+: double τ := by
  obtain ⟨ρ, rfl⟩ := h
  exact ⟨double ρ, (double_append σ ρ).symm⟩

theorem flip_prefix {σ τ : Str} (h : σ <+: τ) : flip σ <+: flip τ := h.map _

theorem not_strElem_le_strBot {σ τ : Str} : ¬ strElem σ ≤ strBot τ := by
  rw [strElem, strBot, C.principal_le_iff]
  exact not_cone_subset_singleton τ σ

theorem strBot_le_strBot_iff {σ τ : Str} : strBot σ ≤ strBot τ ↔ σ <+: τ := by
  rw [strBot, strBot, C.principal_le_iff, cone_subset_cone]

theorem strBot_le_strElem_iff {σ τ : Str} : strBot σ ≤ strElem τ ↔ σ <+: τ := by
  rw [strBot, strElem, C.principal_le_iff]
  exact singleton_subset_cone

theorem strElem_le_strElem_iff {σ τ : Str} : strElem σ ≤ strElem τ ↔ σ = τ := by
  rw [strElem, strElem, C.principal_le_iff, Set.singleton_subset_iff, Set.mem_singleton_iff,
    eq_comm]

end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

def tailSing : Str → C.Element
  | [] => strBot []
  | _ :: σ' => strElem σ'

theorem tail_hsing {σ τ : Str} (h : σ <+: τ) : strBot σ.tail ≤ tailSing τ := by
  cases τ with
  | nil => obtain rfl := List.prefix_nil.mp h; exact le_refl _
  | cons a τ' =>
    refine strBot_le_strElem_iff.mpr ?_
    cases σ with
    | nil => exact List.nil_prefix
    | cons b σ' =>
      obtain ⟨rfl, h'⟩ := List.cons_prefix_cons.mp h
      exact h'

end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

theorem tail_prefix {σ τ : Str} (h : σ <+: τ) : σ.tail <+: τ.tail := by
  obtain ⟨ρ, rfl⟩ := h
  cases σ with
  | nil => simp
  | cons a σ' => exact List.prefix_append σ' ρ
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

theorem tail_hcone {σ τ : Str} (h : σ <+: τ) : strBot σ.tail ≤ strBot τ.tail :=
  strBot_le_strBot_iff.mpr (tail_prefix h)

end
end DomainTheory.NeighbourhoodSystems.Exercise516

section
namespace DomainTheory.NeighbourhoodSystems.Exercise516
section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

def tailMap : ApproximableMap C C :=
  liftC C (fun σ => strBot σ.tail) tailSing tail_hcone tail_hsing

@[simp] theorem tailMap_strBot (σ : Str) :
    tailMap.toElementMap (strBot σ) = strBot σ.tail :=
  liftC_strBot C (fun σ => strBot σ.tail) tailSing tail_hcone tail_hsing σ

@[simp] theorem tailMap_strElem (σ : Str) :
    tailMap.toElementMap (strElem σ) = tailSing σ :=
  liftC_strElem C (fun σ => strBot σ.tail) tailSing tail_hcone tail_hsing σ

theorem neg_hcone {σ τ : Str} (h : σ <+: τ) : strBot (flip σ) ≤ strBot (flip τ) :=
  strBot_le_strBot_iff.mpr (flip_prefix h)

theorem neg_hsing {σ τ : Str} (h : σ <+: τ) : strBot (flip σ) ≤ strElem (flip τ) :=
  strBot_le_strElem_iff.mpr (flip_prefix h)

def negMap : ApproximableMap C C :=
  liftC C (fun σ => strBot (flip σ)) (fun σ => strElem (flip σ)) neg_hcone neg_hsing

@[simp] theorem negMap_strBot (σ : Str) :
    negMap.toElementMap (strBot σ) = strBot (flip σ) :=
  liftC_strBot C (fun σ => strBot (flip σ)) (fun σ => strElem (flip σ)) neg_hcone neg_hsing σ

@[simp] theorem negMap_strElem (σ : Str) :
    negMap.toElementMap (strElem σ) = strElem (flip σ) :=
  liftC_strElem C (fun σ => strBot (flip σ)) (fun σ => strElem (flip σ)) neg_hcone neg_hsing σ

theorem d_hcone {σ τ : Str} (h : σ <+: τ) : strBot (double σ) ≤ strBot (double τ) :=
  strBot_le_strBot_iff.mpr (double_prefix h)

theorem d_hsing {σ τ : Str} (h : σ <+: τ) : strBot (double σ) ≤ strElem (double τ) :=
  strBot_le_strElem_iff.mpr (double_prefix h)

def dMap : ApproximableMap C C :=
  liftC C (fun σ => strBot (double σ)) (fun σ => strElem (double σ)) d_hcone d_hsing

@[simp] theorem dMap_strBot (σ : Str) :
    dMap.toElementMap (strBot σ) = strBot (double σ) :=
  liftC_strBot C (fun σ => strBot (double σ)) (fun σ => strElem (double σ)) d_hcone d_hsing σ

@[simp] theorem dMap_strElem (σ : Str) :
    dMap.toElementMap (strElem σ) = strElem (double σ) :=
  liftC_strElem C (fun σ => strBot (double σ)) (fun σ => strElem (double σ)) d_hcone d_hsing σ

def shape : Bool → Str → Set Str
  | true, σ => {σ}
  | false, σ => cone σ

theorem memC_shape : ∀ (b : Bool) (σ : Str), memC (shape b σ)
  | true, σ => memC_singleton σ
  | false, σ => memC_cone σ

def shapeElem (b : Bool) (σ : Str) : C.Element := C.principal (memC_shape b σ)

@[simp] theorem shapeElem_true (σ : Str) : shapeElem true σ = strElem σ := rfl

@[simp] theorem shapeElem_false (σ : Str) : shapeElem false σ = strBot σ := rfl

def SLe : Bool → Str → Bool → Str → Prop
  | true, σ, b', σ' => b' = true ∧ σ = σ'
  | false, σ, _, σ' => σ <+: σ'

def mergeVal : Str → Bool → Str → Bool → Str × Bool
  | [], b₀, _, _ => ([], b₀)
  | a :: _, _, [], _ => ([a], false)
  | a :: σ, b₀, b :: τ, b₁ => (a :: b :: (mergeVal σ b₀ τ b₁).1, (mergeVal σ b₀ τ b₁).2)

@[simp] theorem mergeVal_nil (b₀ : Bool) (τ : Str) (b₁ : Bool) :
    mergeVal [] b₀ τ b₁ = ([], b₀) := rfl

@[simp] theorem mergeVal_cons_nil (a : Bool) (σ : Str) (b₀ b₁ : Bool) :
    mergeVal (a :: σ) b₀ [] b₁ = ([a], false) := rfl

@[simp] theorem mergeVal_cons_cons (a : Bool) (σ : Str) (b₀ b : Bool) (τ : Str) (b₁ : Bool) :
    mergeVal (a :: σ) b₀ (b :: τ) b₁ =
      (a :: b :: (mergeVal σ b₀ τ b₁).1, (mergeVal σ b₀ τ b₁).2) := rfl

theorem SLe_cons2 {p p' : Bool} {ρ ρ' : Str} (c d : Bool) (h : SLe p ρ p' ρ') :
    SLe p (c :: d :: ρ) p' (c :: d :: ρ') := by
  cases p with
  | true => obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | false =>
    exact List.cons_prefix_cons.mpr ⟨rfl, List.cons_prefix_cons.mpr ⟨rfl, h⟩⟩

theorem SLe_cons_inv {b₀ b₀' : Bool} {a : Bool} {σ₀ σ' : Str} (h : SLe b₀ (a :: σ₀) b₀' σ') :
    ∃ σ₀', σ' = a :: σ₀' ∧ SLe b₀ σ₀ b₀' σ₀' := by
  cases b₀ with
  | true =>
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨σ₀, rfl, rfl, rfl⟩
  | false =>
    cases σ' with
    | nil => exact absurd h (by simp [SLe])
    | cons a' σ₀' =>
      obtain ⟨rfl, h'⟩ := List.cons_prefix_cons.mp h
      exact ⟨σ₀', rfl, h'⟩

def mergeElem (σ : Str) (b₀ : Bool) (τ : Str) (b₁ : Bool) : C.Element :=
  shapeElem (mergeVal σ b₀ τ b₁).2 (mergeVal σ b₀ τ b₁).1

theorem mergeVal_SLe : ∀ (σ : Str) (b₀ : Bool) (σ' : Str) (b₀' : Bool)
    (τ : Str) (b₁ : Bool) (τ' : Str) (b₁' : Bool),
    SLe b₀ σ b₀' σ' → SLe b₁ τ b₁' τ' →
    SLe (mergeVal σ b₀ τ b₁).2 (mergeVal σ b₀ τ b₁).1
      (mergeVal σ' b₀' τ' b₁').2 (mergeVal σ' b₀' τ' b₁').1
  | [], b₀, σ', b₀', τ, b₁, τ', b₁', h0, _ => by
    cases b₀ with
    | true =>
      obtain ⟨rfl, rfl⟩ := h0
      simp only [mergeVal_nil]; exact ⟨rfl, rfl⟩
    | false =>
      simp only [mergeVal_nil]; exact List.nil_prefix
  | a :: σ₀, b₀, σ', b₀', [], b₁, τ', b₁', h0, _ => by
    obtain ⟨σ₀', rfl, _⟩ := SLe_cons_inv h0
    simp only [mergeVal_cons_nil]
    cases τ' with
    | nil => simp only [mergeVal_cons_nil]; exact List.prefix_rfl
    | cons c τ₀' => simp only [mergeVal_cons_cons]; exact ⟨c :: _, rfl⟩
  | a :: σ₀, b₀, σ', b₀', b :: τ₀, b₁, τ', b₁', h0, h1 => by
    obtain ⟨σ₀', rfl, h0'⟩ := SLe_cons_inv h0
    obtain ⟨τ₀', rfl, h1'⟩ := SLe_cons_inv h1
    simp only [mergeVal_cons_cons]
    exact SLe_cons2 a b (mergeVal_SLe σ₀ b₀ σ₀' b₀' τ₀ b₁ τ₀' b₁' h0' h1')

theorem shapeElem_le_iff {b b' : Bool} {σ σ' : Str} :
    shapeElem b σ ≤ shapeElem b' σ' ↔ SLe b σ b' σ' := by
  cases b <;> cases b' <;>
    simp only [shapeElem_true, shapeElem_false, SLe, strElem_le_strElem_iff,
      strBot_le_strBot_iff, strBot_le_strElem_iff, true_and]
  · exact ⟨fun h => absurd h not_strElem_le_strBot, fun h => absurd h (by simp)⟩

theorem mergeElem_mono {σ σ' τ τ' : Str} {b₀ b₀' b₁ b₁' : Bool}
    (h0 : shapeElem b₀ σ ≤ shapeElem b₀' σ') (h1 : shapeElem b₁ τ ≤ shapeElem b₁' τ') :
    mergeElem σ b₀ τ b₁ ≤ mergeElem σ' b₀' τ' b₁' :=
  shapeElem_le_iff.mpr
    (mergeVal_SLe σ b₀ σ' b₀' τ b₁ τ' b₁' (shapeElem_le_iff.mp h0) (shapeElem_le_iff.mp h1))

theorem shape_injective : ∀ {b b' : Bool} {σ σ' : Str}, shape b σ = shape b' σ' → b = b' ∧ σ = σ'
  | true, true, σ, σ', h => ⟨rfl, by rwa [shape, shape, Set.singleton_eq_singleton_iff] at h⟩
  | true, false, σ, σ', h => absurd h.symm (cone_ne_singleton σ' σ)
  | false, true, σ, σ', h => absurd h (cone_ne_singleton σ σ')
  | false, false, σ, σ', h => ⟨rfl, cone_injective h⟩

theorem shape_refine {b : Bool} {σ : Str} {P : Set Str} (hP : memC P) (hsub : P ⊆ shape b σ) :
    ∃ (b' : Bool) (σ' : Str), P = shape b' σ' ∧ shapeElem b σ ≤ shapeElem b' σ' := by
  rcases hP with ⟨ρ, rfl⟩ | ⟨ρ, rfl⟩
  · exact ⟨false, ρ, rfl, (C.principal_le_iff (memC_shape b σ) (memC_shape false ρ)).mpr hsub⟩
  · exact ⟨true, ρ, rfl, (C.principal_le_iff (memC_shape b σ) (memC_shape true ρ)).mpr hsub⟩

def mergeMap : ApproximableMap (prod C C) C where
  rel W Z := ∃ (b₀ : Bool) (σ : Str) (b₁ : Bool) (τ : Str),
    W = prodNbhd (shape b₀ σ) (shape b₁ τ) ∧ (mergeElem σ b₀ τ b₁).mem Z
  rel_dom := by
    rintro W Z ⟨b₀, σ, b₁, τ, rfl, _⟩
    exact prod_mem_prodNbhd (memC_shape b₀ σ) (memC_shape b₁ τ)
  rel_cod := by
    rintro W Z ⟨b₀, σ, b₁, τ, _, hZ⟩
    exact (mergeElem σ b₀ τ b₁).sub hZ
  master_rel := by
    refine ⟨false, [], false, [], ?_, (mergeElem [] false [] false).master_mem⟩
    show (prod C C).master = prodNbhd (shape false []) (shape false [])
    simp only [prod_master, shape, C_master, cone_nil]
  inter_right := by
    rintro W Z Z' ⟨b₀, σ, b₁, τ, rfl, hZ⟩ ⟨b₀', σ', b₁', τ', heq, hZ'⟩
    obtain ⟨hX, hY⟩ := prodNbhd_injective heq
    obtain ⟨rfl, rfl⟩ := shape_injective hX
    obtain ⟨rfl, rfl⟩ := shape_injective hY
    exact ⟨b₀, σ, b₁, τ, rfl, (mergeElem σ b₀ τ b₁).inter_mem hZ hZ'⟩
  mono := by
    rintro W W₂ Z Z' ⟨b₀, σ, b₁, τ, rfl, hZ⟩ hW₂W hZZ' hW₂ hZ'
    obtain ⟨P, Q, hP, hQ, rfl⟩ := hW₂
    obtain ⟨hPsub, hQsub⟩ := prodNbhd_subset_iff.mp hW₂W
    obtain ⟨b₀', σ', hPeq, hle0⟩ := shape_refine hP hPsub
    obtain ⟨b₁', τ', hQeq, hle1⟩ := shape_refine hQ hQsub
    subst hPeq; subst hQeq
    refine ⟨b₀', σ', b₁', τ', rfl, ?_⟩
    have hmono := mergeElem_mono hle0 hle1
    exact (mergeElem σ' b₀' τ' b₁').up_mem (hmono Z hZ) hZ' hZZ'

@[simp] theorem consMap_shapeElem (b c : Bool) (σ : Str) :
    (consMap b).toElementMap (shapeElem c σ) = shapeElem c (b :: σ) := by
  cases c with
  | false => rw [shapeElem_false, consMap_strBot]; rfl
  | true => rw [shapeElem_true, consMap_strElem]; rfl

theorem map_ext_C {V : NeighborhoodSystem β} {f g : ApproximableMap C V}
    (hbot : ∀ σ, f.toElementMap (strBot σ) = g.toElementMap (strBot σ))
    (helem : ∀ σ, f.toElementMap (strElem σ) = g.toElementMap (strElem σ)) : f = g := by
  apply eq_of_toElementMap_principal
  intro X hX
  obtain (⟨σ, rfl⟩ | ⟨σ, rfl⟩) := (C_mem.mp hX)
  · exact hbot σ
  · exact helem σ

theorem memC_eq_shape {X : Set Str} (hX : memC X) : ∃ (b : Bool) (σ : Str), X = shape b σ := by
  rcases hX with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
  · exact ⟨false, σ, rfl⟩
  · exact ⟨true, σ, rfl⟩

theorem mergeMap_pair (b₀ : Bool) (σ : Str) (b₁ : Bool) (τ : Str) :
    mergeMap.toElementMap (pair (shapeElem b₀ σ) (shapeElem b₁ τ)) = mergeElem σ b₀ τ b₁ := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨W, hWmem, c₀, ρ, c₁, π, rfl, hZ⟩
    rw [mem_pair_prodNbhd] at hWmem
    obtain ⟨hmσ, hmτ⟩ := hWmem
    have hle0 : shapeElem c₀ ρ ≤ shapeElem b₀ σ :=
      (C.principal_le_iff (memC_shape c₀ ρ) (memC_shape b₀ σ)).mpr hmσ.2
    have hle1 : shapeElem c₁ π ≤ shapeElem b₁ τ :=
      (C.principal_le_iff (memC_shape c₁ π) (memC_shape b₁ τ)).mpr hmτ.2
    exact mergeElem_mono hle0 hle1 Z hZ
  · intro hZ
    refine ⟨prodNbhd (shape b₀ σ) (shape b₁ τ), ?_, b₀, σ, b₁, τ, rfl, hZ⟩
    exact mem_pair_prodNbhd.mpr ⟨⟨memC_shape b₀ σ, subset_rfl⟩, ⟨memC_shape b₁ τ, subset_rfl⟩⟩

theorem mergeVal_diag (s : Bool) (σ : Str) : mergeVal σ s σ s = (double σ, s) := by
  induction σ with
  | nil => rfl
  | cons a σ ih => simp [mergeVal_cons_cons, ih]

theorem mergeElem_diag (s : Bool) (σ : Str) : mergeElem σ s σ s = shapeElem s (double σ) := by
  simp [mergeElem, mergeVal_diag]

theorem mergeMap_diag (x : C.Element) :
    mergeMap.toElementMap (pair x x) = dMap.toElementMap x := by
  have key : mergeMap.comp (paired (idMap C) (idMap C)) = dMap := by
    apply map_ext_C
    · intro σ
      rw [toElementMap_comp, toElementMap_paired, toElementMap_idMap,
        show pair (strBot σ) (strBot σ) = pair (shapeElem false σ) (shapeElem false σ) from rfl,
        mergeMap_pair, mergeElem_diag, shapeElem_false, dMap_strBot]
    · intro σ
      rw [toElementMap_comp, toElementMap_paired, toElementMap_idMap,
        show pair (strElem σ) (strElem σ) = pair (shapeElem true σ) (shapeElem true σ) from rfl,
        mergeMap_pair, mergeElem_diag, shapeElem_true, dMap_strElem]
  have hx := congrArg (fun m : ApproximableMap C C => m.toElementMap x) key
  simp only [toElementMap_comp, toElementMap_paired, toElementMap_idMap] at hx
  exact hx

theorem negMap_comp_negMap : negMap.comp negMap = idMap C := by
  apply map_ext_C
  · intro σ
    rw [toElementMap_comp, negMap_strBot, negMap_strBot, flip_flip, toElementMap_idMap]
  · intro σ
    rw [toElementMap_comp, negMap_strElem, negMap_strElem, flip_flip, toElementMap_idMap]

theorem negMap_negMap (x : C.Element) : negMap.toElementMap (negMap.toElementMap x) = x := by
  have h := negMap_comp_negMap
  rw [← toElementMap_comp, h, toElementMap_idMap]

theorem neg_cons_false : negMap.comp (consMap false) = (consMap true).comp negMap := by
  apply map_ext_C
  · intro σ
    rw [toElementMap_comp, consMap_strBot, negMap_strBot, toElementMap_comp, negMap_strBot,
      consMap_strBot]
    rfl
  · intro σ
    rw [toElementMap_comp, consMap_strElem, negMap_strElem, toElementMap_comp, negMap_strElem,
      consMap_strElem]
    rfl

theorem neg_cons_true : negMap.comp (consMap true) = (consMap false).comp negMap := by
  apply map_ext_C
  · intro σ
    rw [toElementMap_comp, consMap_strBot, negMap_strBot, toElementMap_comp, negMap_strBot,
      consMap_strBot]
    rfl
  · intro σ
    rw [toElementMap_comp, consMap_strElem, negMap_strElem, toElementMap_comp, negMap_strElem,
      consMap_strElem]
    rfl

theorem prod_principal_pair (b₀ : Bool) (σ : Str) (b₁ : Bool) (τ : Str) :
    (prod C C).principal (prod_mem_prodNbhd (memC_shape b₀ σ) (memC_shape b₁ τ))
      = pair (shapeElem b₀ σ) (shapeElem b₁ τ) := by
  apply Element.ext
  intro P
  rw [mem_principal]
  constructor
  · rintro ⟨hP, hsub⟩
    obtain ⟨X', Y', hX', hY', rfl⟩ := hP
    obtain ⟨hsX, hsY⟩ := prodNbhd_subset_iff.mp hsub
    exact ⟨X', Y', ⟨hX', hsX⟩, ⟨hY', hsY⟩, rfl⟩
  · rintro ⟨X', Y', ⟨hX', hsX⟩, ⟨hY', hsY⟩, rfl⟩
    exact ⟨prod_mem_prodNbhd hX' hY', prodNbhd_subset_iff.mpr ⟨hsX, hsY⟩⟩

theorem prodMap_ext {f g : ApproximableMap (prod C C) C}
    (h : ∀ b₀ σ b₁ τ, f.toElementMap (pair (shapeElem b₀ σ) (shapeElem b₁ τ))
      = g.toElementMap (pair (shapeElem b₀ σ) (shapeElem b₁ τ))) : f = g := by
  apply eq_of_toElementMap_principal
  intro W hW
  obtain ⟨b₀, σ, b₁, τ, rfl⟩ :
      ∃ b₀ σ b₁ τ, W = prodNbhd (shape b₀ σ) (shape b₁ τ) := by
    obtain ⟨X, Y, hX, hY, rfl⟩ := hW
    obtain ⟨b₀, σ, rfl⟩ := memC_eq_shape hX
    obtain ⟨b₁, τ, rfl⟩ := memC_eq_shape hY
    exact ⟨b₀, σ, b₁, τ, rfl⟩
  have heq : (prod C C).principal hW = pair (shapeElem b₀ σ) (shapeElem b₁ τ) :=
    prod_principal_pair b₀ σ b₁ τ
  rw [heq]; exact h b₀ σ b₁ τ

theorem mergeMap_cons (ε δ : Bool) (x y : C.Element) :
    mergeMap.toElementMap
        (pair ((consMap ε).toElementMap x) ((consMap δ).toElementMap y))
      = (consMap ε).toElementMap
          ((consMap δ).toElementMap (mergeMap.toElementMap (pair x y))) := by
  have key :
      mergeMap.comp (paired ((consMap ε).comp (proj₀ C C)) ((consMap δ).comp (proj₁ C C)))
        = ((consMap ε).comp (consMap δ)).comp mergeMap := by
    apply prodMap_ext
    intro b₀ σ b₁ τ
    simp only [toElementMap_comp, toElementMap_paired, toElementMap_proj₀, toElementMap_proj₁,
      fst_pair, snd_pair, consMap_shapeElem, mergeMap_pair, mergeElem, mergeVal_cons_cons]
  have hx := congrArg (fun m : ApproximableMap (prod C C) C => m.toElementMap (pair x y)) key
  simp only [toElementMap_comp, toElementMap_paired, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair] at hx
  exact hx

end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

theorem tailMap_consMap_strBot (b : Bool) (σ : Str) :
    tailMap.toElementMap ((consMap b).toElementMap (strBot σ)) = strBot σ := by
  rw [consMap_strBot, tailMap_strBot]; rfl

theorem tailMap_consMap_strElem (b : Bool) (σ : Str) :
    tailMap.toElementMap ((consMap b).toElementMap (strElem σ)) = strElem σ := by
  rw [consMap_strElem, tailMap_strElem]; rfl

end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

def expand : Str → Str
  | [] => []
  | b :: σ => b :: (!b) :: expand σ

@[simp] theorem expand_nil : expand [] = [] := rfl

@[simp] theorem expand_cons (b : Bool) (σ : Str) : expand (b :: σ) = b :: (!b) :: expand σ := rfl

def tm (n : ℕ) : Bool := (Nat.bits n).foldr xor false

def tmOp : ApproximableMap C C :=
  (consMap false).comp (mergeMap.comp (paired negMap tailMap))

@[simp] theorem tm_zero : tm 0 = false := by simp [tm, Nat.zero_bits]

def tmList (n : ℕ) : Str := (List.range n).map tm

@[simp] theorem tmList_zero : tmList 0 = [] := rfl

def tElt : C.Element := tmOp.fixElement

theorem cone_univ_iff {σ : Str} : cone σ = Set.univ ↔ σ = [] := by
  constructor
  · intro h
    exact List.prefix_nil.mp (mem_cone.mp (h ▸ Set.mem_univ ([] : Str)))
  · rintro rfl; exact cone_nil

theorem expand_append (σ τ : Str) : expand (σ ++ τ) = expand σ ++ expand τ := by
  induction σ with
  | nil => rfl
  | cons b σ ih => simp [ih]

theorem iterate_expand_cons (k : ℕ) : ∃ ρ, (expand^[k] [false] : Str) = false :: ρ := by
  induction k with
  | zero => exact ⟨[], rfl⟩
  | succ k ih =>
    obtain ⟨ρ, hρ⟩ := ih
    exact ⟨true :: expand ρ, by rw [Function.iterate_succ_apply', hρ]; rfl⟩

theorem mergeVal_snd_false : ∀ (σ τ : Str) (b₁ : Bool), (mergeVal σ false τ b₁).2 = false
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: σ, _ :: τ, b₁ => by simp only [mergeVal_cons_cons]; exact mergeVal_snd_false σ τ b₁

theorem strBot_mem_cone {σ τ : Str} : (strBot τ).mem (cone σ) ↔ σ <+: τ := by
  rw [strBot, mem_principal]
  exact ⟨fun h => cone_subset_cone.mp h.2, fun h => ⟨memC_cone σ, cone_subset_cone.mpr h⟩⟩

theorem strBot_nil : strBot [] = C.bot := by
  apply Element.ext
  intro Y
  rw [strBot, mem_principal, mem_bot, cone_nil, C_master]
  exact ⟨fun h => Set.Subset.antisymm (Set.subset_univ _) h.2,
    fun h => ⟨h ▸ C.master_mem, h ▸ Set.Subset.refl _⟩⟩

theorem tElt_unfold :
    (consMap false).toElementMap
        (mergeMap.toElementMap (pair (negMap.toElementMap tElt) (tailMap.toElementMap tElt)))
      = tElt := by
  have h := toElementMap_fixElement tmOp
  rw [tmOp, toElementMap_comp, toElementMap_comp, toElementMap_paired] at h
  exact h

theorem tmList_length (n : ℕ) : (tmList n).length = n := by
  rw [tmList, List.length_map, List.length_range]

theorem tmList_succ (n : ℕ) : tmList (n + 1) = tmList n ++ [tm n] := by
  simp only [tmList, List.range_succ, List.map_append, List.map_cons, List.map_nil]

theorem tmList_prefix {n m : ℕ} (h : n ≤ m) : tmList n <+: tmList m := by
  induction m with
  | zero => rw [Nat.le_zero.mp h]
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with hlt | rfl
    · exact (ih (Nat.lt_succ_iff.mp hlt)).trans (by rw [tmList_succ]; exact List.prefix_append _ _)
    · exact List.prefix_rfl

theorem tmOp_strBot (σ : Str) :
    tmOp.toElementMap (strBot σ)
      = strBot (false :: (mergeVal (flip σ) false σ.tail false).1) := by
  unfold tmOp
  rw [toElementMap_comp, toElementMap_comp, toElementMap_paired, negMap_strBot, tailMap_strBot,
    show (strBot (flip σ)) = shapeElem false (flip σ) from rfl,
    show (strBot σ.tail) = shapeElem false σ.tail from rfl, mergeMap_pair, mergeElem,
    mergeVal_snd_false, shapeElem_false, consMap_strBot]

theorem tm_two_mul (n : ℕ) : tm (2 * n) = tm n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · simp only [tm, Nat.bit0_bits n (by omega : n ≠ 0), List.foldr_cons, Bool.false_xor]

theorem tm_two_mul_add_one (n : ℕ) : tm (2 * n + 1) = !tm n := by
  simp only [tm, Nat.bit1_bits n, List.foldr_cons, Bool.true_xor]

theorem expand_tmList (m : ℕ) : expand (tmList m) = tmList (2 * m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have key : tmList (2 * (m + 1)) = tmList (2 * m) ++ [tm m, !tm m] := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, tmList_succ, tmList_succ,
        tm_two_mul_add_one, tm_two_mul, List.append_assoc]
      rfl
    rw [tmList_succ, expand_append, ih, key, expand_cons, expand_nil]

theorem expand_iterate_eq (k : ℕ) : (expand^[k] [false] : Str) = tmList (2 ^ k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, expand_tmList, show 2 * 2 ^ k = 2 ^ (k + 1) by ring]

theorem weave_head : ∀ (h : Bool) (ρ : Str), (mergeVal (h :: flip ρ) false ρ false).1 = h :: expand ρ
  | h, [] => rfl
  | h, c :: ρ => by
    simp only [flip_cons, mergeVal_cons_cons, expand_cons]
    rw [weave_head (!c) ρ]

theorem tmOp_strBot_expand (ρ : Str) :
    tmOp.toElementMap (strBot (false :: ρ)) = strBot (expand (false :: ρ)) := by
  rw [tmOp_strBot]
  simp only [flip_cons, List.tail_cons, expand_cons]
  rw [weave_head (!false) ρ]

theorem iterElem_succ_eq (k : ℕ) :
    tmOp.iterElem (k + 1) = strBot (expand^[k] [false]) := by
  induction k with
  | zero =>
    rw [iterElem_succ, iterElem_zero, ← strBot_nil, tmOp_strBot]
    rfl
  | succ k ih =>
    obtain ⟨ρ, hρ⟩ := iterate_expand_cons k
    rw [iterElem_succ, ih, hρ, tmOp_strBot_expand, ← hρ, Function.iterate_succ_apply']

end

section
open DomainTheory.NeighbourhoodSystems

def Overlap (i p : ℕ) : Prop := 1 ≤ p ∧ ∀ k, k ≤ p → tm (i + k) = tm (i + p + k)
end

section
open DomainTheory.NeighbourhoodSystems
open Example44 ExampleB NeighborhoodSystem

theorem append_three_period {α : Type*} (a : List α) (m : ℕ) (hm : m < 2 * a.length) :
    (a ++ (a ++ a))[m]? = (a ++ (a ++ a))[m + a.length]? := by
  rcases lt_or_ge m a.length with h | h
  · rw [List.getElem?_append_left h,
      List.getElem?_append_right (by omega : a.length ≤ m + a.length),
      show m + a.length - a.length = m by omega, List.getElem?_append_left h]
  · rw [List.getElem?_append_right h,
      List.getElem?_append_right (by omega : a.length ≤ m + a.length),
      show m + a.length - a.length = m by omega,
      List.getElem?_append_left (by omega : m - a.length < a.length),
      List.getElem?_append_right (by omega : a.length ≤ m)]

theorem tmList_getElem? {n j : ℕ} (h : j < n) : (tmList n)[j]? = some (tm j) := by
  rw [tmList, List.getElem?_map, List.getElem?_range h]
  rfl

end

section
open DomainTheory.NeighbourhoodSystems

theorem tm_of_eq_two_mul {x y : ℕ} (h : x = 2 * y) : tm x = tm y := by
  rw [h, tm_two_mul]

theorem tm_of_eq_two_mul_add_one {x y : ℕ} (h : x = 2 * y + 1) : tm x = !tm y := by
  rw [h, tm_two_mul_add_one]

theorem tm_two_mul_ne (x : ℕ) : tm (2 * x) ≠ tm (2 * x + 1) := by
  rw [tm_two_mul, tm_two_mul_add_one]
  cases tm x <;> simp

theorem odd_of_consec_eq {x : ℕ} (h : tm x = tm (x + 1)) : Odd x := by
  rcases Nat.even_or_odd x with ⟨m, hm⟩ | hodd
  · exfalso; rw [hm, ← two_mul] at h; exact tm_two_mul_ne m h
  · exact hodd

theorem no_three_consec (j : ℕ) : ¬ (tm j = tm (j + 1) ∧ tm (j + 1) = tm (j + 2)) := by
  rintro ⟨h1, h2⟩
  have hj : Odd j := odd_of_consec_eq h1
  have hj1 : Odd (j + 1) := odd_of_consec_eq h2
  rcases hj with ⟨a, rfl⟩
  rcases hj1 with ⟨b, hb⟩
  omega

theorem no_overlap (p : ℕ) : ∀ i, ¬ Overlap i p := by
  induction p using Nat.strong_induction_on with
  | _ p IH =>
    intro i hov
    obtain ⟨hp1, hrel⟩ := hov
    obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' p
    ·
      subst hq
      have hq1 : 1 ≤ q := by omega
      obtain ⟨a, hi | hi⟩ := Nat.even_or_odd' i
      ·
        refine IH q (by omega) a ⟨hq1, fun c hc => ?_⟩
        have hk : 2 * c ≤ 2 * q := by omega
        have := hrel (2 * c) hk
        rw [tm_of_eq_two_mul (show i + 2 * c = 2 * (a + c) by omega),
          tm_of_eq_two_mul (show i + 2 * q + 2 * c = 2 * (a + q + c) by omega)] at this
        exact this
      ·
        refine IH q (by omega) a ⟨hq1, fun c hc => ?_⟩
        have hk : 2 * c ≤ 2 * q := by omega
        have := hrel (2 * c) hk
        rw [tm_of_eq_two_mul_add_one (show i + 2 * c = 2 * (a + c) + 1 by omega),
          tm_of_eq_two_mul_add_one (show i + 2 * q + 2 * c = 2 * (a + q + c) + 1 by omega)] at this
        exact Bool.not_inj this
    ·
      subst hq
      rcases Nat.eq_zero_or_pos q with rfl | hq1
      ·
        refine no_three_consec i ⟨?_, ?_⟩
        · have := hrel 0 (by omega); simpa using this
        · have := hrel 1 (by omega); simpa [show i + 1 + 1 = i + 2 by omega] using this
      ·
        obtain ⟨a, hi | hi⟩ := Nat.even_or_odd' i
        ·
          subst hi
          have r0 := hrel 0 (by omega)
          have r1 := hrel 1 (by omega)
          have r2 := hrel 2 (by omega)
          have r3 := hrel 3 (by omega)
          rw [tm_of_eq_two_mul (show 2 * a + 0 = 2 * a by omega),
            tm_of_eq_two_mul_add_one (show 2 * a + (2 * q + 1) + 0 = 2 * (a + q) + 1 by omega)] at r0
          rw [tm_of_eq_two_mul_add_one (show 2 * a + 1 = 2 * a + 1 by omega),
            tm_of_eq_two_mul (show 2 * a + (2 * q + 1) + 1 = 2 * (a + q + 1) by omega)] at r1
          rw [tm_of_eq_two_mul (show 2 * a + 2 = 2 * (a + 1) by omega),
            tm_of_eq_two_mul_add_one
              (show 2 * a + (2 * q + 1) + 2 = 2 * (a + q + 1) + 1 by omega)] at r2
          rw [tm_of_eq_two_mul_add_one (show 2 * a + 3 = 2 * (a + 1) + 1 by omega),
            tm_of_eq_two_mul (show 2 * a + (2 * q + 1) + 3 = 2 * (a + q + 2) by omega)] at r3
          refine no_three_consec (a + q) ⟨?_, ?_⟩
          · revert r0 r1; cases tm a <;> cases tm (a + q) <;> cases tm (a + q + 1) <;>
              simp_all
          · revert r1 r2 r3
            cases tm (a + 1) <;> cases tm (a + q + 1) <;> cases tm (a + q + 2) <;> cases tm a <;>
              simp_all
        ·
          subst hi
          rcases Nat.eq_or_lt_of_le hq1 with hq2 | hq2
          ·
            subst hq2
            have r0 := hrel 0 (by omega)
            have r1 := hrel 1 (by omega)
            have r2 := hrel 2 (by omega)
            have r3 := hrel 3 (by omega)
            rw [tm_of_eq_two_mul_add_one (show 2 * a + 1 + 0 = 2 * a + 1 by omega),
              tm_of_eq_two_mul (show 2 * a + 1 + (2 * 1 + 1) + 0 = 2 * (a + 2) by omega)] at r0
            rw [tm_of_eq_two_mul (show 2 * a + 1 + 1 = 2 * (a + 1) by omega),
              tm_of_eq_two_mul_add_one
                (show 2 * a + 1 + (2 * 1 + 1) + 1 = 2 * (a + 2) + 1 by omega)] at r1
            rw [tm_of_eq_two_mul_add_one (show 2 * a + 1 + 2 = 2 * (a + 1) + 1 by omega),
              tm_of_eq_two_mul (show 2 * a + 1 + (2 * 1 + 1) + 2 = 2 * (a + 3) by omega)] at r2
            rw [tm_of_eq_two_mul (show 2 * a + 1 + 3 = 2 * (a + 2) by omega),
              tm_of_eq_two_mul_add_one
                (show 2 * a + 1 + (2 * 1 + 1) + 3 = 2 * (a + 3) + 1 by omega)] at r3
            revert r0 r1 r2 r3
            cases tm a <;> cases tm (a + 1) <;> cases tm (a + 2) <;> cases tm (a + 3) <;> simp_all
          ·
            have r1 := hrel 1 (by omega)
            have r2 := hrel 2 (by omega)
            have r3 := hrel 3 (by omega)
            have r4 := hrel 4 (by omega)
            rw [tm_of_eq_two_mul (show 2 * a + 1 + 1 = 2 * (a + 1) by omega),
              tm_of_eq_two_mul_add_one
                (show 2 * a + 1 + (2 * q + 1) + 1 = 2 * (a + q + 1) + 1 by omega)] at r1
            rw [tm_of_eq_two_mul_add_one (show 2 * a + 1 + 2 = 2 * (a + 1) + 1 by omega),
              tm_of_eq_two_mul
                (show 2 * a + 1 + (2 * q + 1) + 2 = 2 * (a + q + 2) by omega)] at r2
            rw [tm_of_eq_two_mul (show 2 * a + 1 + 3 = 2 * (a + 2) by omega),
              tm_of_eq_two_mul_add_one
                (show 2 * a + 1 + (2 * q + 1) + 3 = 2 * (a + q + 2) + 1 by omega)] at r3
            rw [tm_of_eq_two_mul_add_one (show 2 * a + 1 + 4 = 2 * (a + 2) + 1 by omega),
              tm_of_eq_two_mul
                (show 2 * a + 1 + (2 * q + 1) + 4 = 2 * (a + q + 3) by omega)] at r4
            refine no_three_consec (a + q + 1) ⟨?_, ?_⟩
            · revert r1 r2; cases tm (a + 1) <;> cases tm (a + q + 1) <;> cases tm (a + q + 2) <;>
                simp_all
            · revert r3 r4; cases tm (a + 2) <;> cases tm (a + q + 2) <;> cases tm (a + q + 3) <;>
                simp_all

theorem no_cube (i p : ℕ) (hp : 1 ≤ p) :
    ¬ ∀ k, k < 2 * p → tm (i + k) = tm (i + p + k) := by
  intro hcube
  exact no_overlap p i ⟨hp, fun k hk => hcube k (by omega)⟩

end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

theorem tmList_le_tElt (n : ℕ) : strBot (tmList n) ≤ tElt := by
  have hpre : tmList n <+: expand^[n] [false] := by
    rw [expand_iterate_eq]; exact tmList_prefix (Nat.le_of_lt (Nat.lt_two_pow_self))
  calc strBot (tmList n) ≤ strBot (expand^[n] [false]) :=
        strBot_le_strBot_iff.mpr hpre
    _ = tmOp.iterElem (n + 1) := (iterElem_succ_eq n).symm
    _ ≤ tElt := iterElem_le_fixElement tmOp (n + 1)

theorem tElt_digit (n : ℕ) : strBot (tmList n ++ [tm n]) ≤ tElt := by
  have h := tmList_le_tElt (n + 1)
  rwa [tmList_succ] at h

theorem tElt_mem_cone_iff (σ : Str) : tElt.mem (cone σ) ↔ σ = tmList σ.length := by
  constructor
  · intro hσ
    rw [show tElt = tmOp.fixElement from rfl, tmOp.fixElement_eq_iSupDirected,
      mem_iSupDirected] at hσ
    obtain ⟨n, hn⟩ := hσ

    obtain ⟨N, hpre⟩ : ∃ N, σ <+: tmList N := by
      cases n with
      | zero =>
        rw [iterElem_zero, mem_bot, C_master, cone_univ_iff] at hn
        exact ⟨0, by rw [hn]; exact List.nil_prefix⟩
      | succ k =>
        rw [iterElem_succ_eq, strBot_mem_cone, expand_iterate_eq] at hn
        exact ⟨2 ^ k, hn⟩

    have hlen : σ.length ≤ N := hpre.length_le.trans_eq (tmList_length _)
    have h1 : σ = (tmList N).take σ.length := List.prefix_iff_eq_take.mp hpre
    have h2 : tmList σ.length = (tmList N).take σ.length := by
      have := List.prefix_iff_eq_take.mp (tmList_prefix hlen)
      rwa [tmList_length] at this
    exact h1.trans h2.symm
  · intro hσ
    have h := tmList_le_tElt σ.length
    have hmem : (strBot (tmList σ.length)).mem (cone σ) :=
      strBot_mem_cone.mpr (hσ ▸ List.prefix_rfl)
    exact h _ hmem

end

section
open DomainTheory.NeighbourhoodSystems
open Example44 ExampleB NeighborhoodSystem

theorem tElt_cube_free (u a : Str) (ha : a ≠ []) :
    ¬ strBot (u ++ a ++ a ++ a) ≤ tElt := by
  intro hle

  have hmem : tElt.mem (cone (u ++ a ++ a ++ a)) :=
    hle _ (strBot_mem_cone.mpr List.prefix_rfl)
  have heq : u ++ a ++ a ++ a = tmList (u ++ a ++ a ++ a).length :=
    (tElt_mem_cone_iff _).mp hmem

  set N := (u ++ a ++ a ++ a).length with hN
  have hlen : N = u.length + 3 * a.length := by simp only [hN, List.length_append]; omega
  have hp : 1 ≤ a.length := by
    cases a with
    | nil => exact (ha rfl).elim
    | cons _ _ => simp
  refine no_cube u.length a.length hp (fun k hk => ?_)

  have hk3 : u.length + k < N := by omega
  have hk3' : u.length + a.length + k < N := by omega
  have e1 : (tmList N)[u.length + k]? = some (tm (u.length + k)) := tmList_getElem? hk3
  have e2 : (tmList N)[u.length + a.length + k]? = some (tm (u.length + a.length + k)) :=
    tmList_getElem? hk3'

  have hassoc : u ++ a ++ a ++ a = u ++ (a ++ (a ++ a)) := by
    simp [List.append_assoc]
  rw [← heq, hassoc] at e1 e2
  rw [List.getElem?_append_right (by omega : u.length ≤ u.length + k),
    show u.length + k - u.length = k by omega] at e1
  rw [List.getElem?_append_right (by omega : u.length ≤ u.length + a.length + k),
    show u.length + a.length + k - u.length = k + a.length by omega] at e2

  have hper := append_three_period a k (by omega)
  have : some (tm (u.length + k)) = some (tm (u.length + a.length + k)) := by
    rw [← e1, hper, e2]
  exact Option.some.inj this
end

end DomainTheory.NeighbourhoodSystems.Exercise516
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

def pfix (τ : ApproximableMap (prod V V) V) : ApproximableMap V V :=
  (fixMap V).comp (curry τ)

def recOp (τ : ApproximableMap (prod V V) V) : ApproximableMap (funSpace V V) (funSpace V V) :=
  curry (τ.comp (paired (proj₁ (funSpace V V) V) (evalMap V V)))

def section₂ (τ : ApproximableMap (prod V V) V) (x : V.Element) : ApproximableMap V V :=
  toApproxMap ((curry τ).toElementMap x)

theorem pfix_apply (τ : ApproximableMap (prod V V) V) (x : V.Element) :
    (pfix τ).toElementMap x = (section₂ τ x).fixElement := by
  rw [pfix, toElementMap_comp, fixMap_toElementMap, section₂]

theorem recOp_apply (τ : ApproximableMap (prod V V) V) (φ : (funSpace V V).Element) (x : V.Element) :
    (toApproxMap ((recOp τ).toElementMap φ)).toElementMap x
      = τ.toElementMap (pair x ((toApproxMap φ).toElementMap x)) := by
  rw [recOp, toElementMap_curry_apply, toElementMap_comp, toElementMap_paired,
    toElementMap_proj₁, snd_pair, evalMap_apply]

theorem section₂_apply (τ : ApproximableMap (prod V V) V) (x y : V.Element) :
    (section₂ τ x).toElementMap y = τ.toElementMap (pair x y) := by
  rw [section₂, toElementMap_curry_apply]

theorem pfix_isFixed (τ : ApproximableMap (prod V V) V) (x : V.Element) :
    τ.toElementMap (pair x ((pfix τ).toElementMap x)) = (pfix τ).toElementMap x := by
  rw [pfix_apply, ← section₂_apply, toElementMap_fixElement]

end ApproximableMap
end
end DomainTheory.NeighbourhoodSystems
end

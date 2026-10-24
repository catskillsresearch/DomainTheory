module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_19
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_2
public import Mathlib.Data.Nat.Bits
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_7

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise516
section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- Complement every bit of a finite string. -/
abbrev flip (σ : Str) : Str := σ.map not

@[simp] theorem flip_nil : flip [] = [] := rfl

@[simp] theorem flip_cons (b : Bool) (σ : Str) : flip (b :: σ) = (!b) :: flip σ := rfl

@[simp] theorem flip_flip (σ : Str) : flip (flip σ) = σ := by
  induction σ with
  | nil => rfl
  | cons b σ ih => simp [ih]

/-- Double every bit of a finite string: `double (b :: σ) = b :: b :: double σ`. -/
def double : Str → Str
  | [] => []
  | b :: σ => b :: b :: double σ

@[simp] theorem double_nil : double [] = [] := rfl

@[simp] theorem double_cons (b : Bool) (σ : Str) : double (b :: σ) = b :: b :: double σ := rfl

/-- `double` distributes over append. -/
theorem double_append (σ τ : Str) : double (σ ++ τ) = double σ ++ double τ := by
  induction σ with
  | nil => rfl
  | cons b σ ih => simp [double, ih]

/-- `double` preserves the prefix order. -/
theorem double_prefix {σ τ : Str} (h : σ <+: τ) : double σ <+: double τ := by
  obtain ⟨ρ, rfl⟩ := h
  exact ⟨double ρ, (double_append σ ρ).symm⟩

/-- `flip` preserves the prefix order. -/
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

/-- The value of `tail` on a total element `σ`: `tail(Λ) = ⊥`, `tail(bσ') = σ'`. -/
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

/-- A prefix relation descends to tails. -/
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

/- concordance: source L3184 EXERCISE 5.16 negation of sequences -/
/-- **Exercise 5.16 / Example 4.4 — `tail : C → C`.** Built with the head-test combinator `liftC`:
on `σ⊥` it returns `(tail σ)⊥`, on `σ` the total `tail σ` (with `tail Λ = ⊥`). -/
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

/-- **Exercise 5.16 — `neg : C → C`.** The closed-form solution of Scott's recursion, built with
`liftC`: `neg(σ⊥) = (flip σ)⊥` and `neg(σ) = flip σ`. -/
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

/-- **Exercise 5.16 / Example 4.4 — `d : C → C`.** The doubling map, closed form via `liftC`:
`d(σ⊥) = (double σ)⊥`, `d(σ) = double σ`. -/
def dMap : ApproximableMap C C :=
  liftC C (fun σ => strBot (double σ)) (fun σ => strElem (double σ)) d_hcone d_hsing

@[simp] theorem dMap_strBot (σ : Str) :
    dMap.toElementMap (strBot σ) = strBot (double σ) :=
  liftC_strBot C (fun σ => strBot (double σ)) (fun σ => strElem (double σ)) d_hcone d_hsing σ

@[simp] theorem dMap_strElem (σ : Str) :
    dMap.toElementMap (strElem σ) = strElem (double σ) :=
  liftC_strElem C (fun σ => strBot (double σ)) (fun σ => strElem (double σ)) d_hcone d_hsing σ

/-- The neighbourhood of the tagged string `(b, σ)`: `{σ}` if total, `cone σ` if partial. -/
def shape : Bool → Str → Set Str
  | true, σ => {σ}
  | false, σ => cone σ

theorem memC_shape : ∀ (b : Bool) (σ : Str), memC (shape b σ)
  | true, σ => memC_singleton σ
  | false, σ => memC_cone σ

/-- The element of the tagged string `(b, σ)`: total `σ` if `b`, partial `σ⊥` otherwise. -/
def shapeElem (b : Bool) (σ : Str) : C.Element := C.principal (memC_shape b σ)

@[simp] theorem shapeElem_true (σ : Str) : shapeElem true σ = strElem σ := rfl

@[simp] theorem shapeElem_false (σ : Str) : shapeElem false σ = strBot σ := rfl

/-- The approximation order between tagged strings: `(b, σ) ⊑ (b', σ')`. A total string is maximal
(only `⊑` itself); a partial string `σ⊥` is `⊑` anything extending `σ`. -/
def SLe : Bool → Str → Bool → Str → Prop
  | true, σ, b', σ' => b' = true ∧ σ = σ'
  | false, σ, _, σ' => σ <+: σ'

/-- The interleave value function: `mergeVal σ b₀ τ b₁` returns the interleaving of the tagged
strings `(b₀, σ)` and `(b₁, τ)` as a tagged string. Boundary convention (the only monotone one):
`merge(Λ, y) = Λ`, `merge(⊥, y) = ⊥`, and `merge(εx, y) = ε⊥` once `y` runs out. -/
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

/-- Two equal head bits prepended preserve `SLe`. -/
theorem SLe_cons2 {p p' : Bool} {ρ ρ' : Str} (c d : Bool) (h : SLe p ρ p' ρ') :
    SLe p (c :: d :: ρ) p' (c :: d :: ρ') := by
  cases p with
  | true => obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | false =>
    exact List.cons_prefix_cons.mpr ⟨rfl, List.cons_prefix_cons.mpr ⟨rfl, h⟩⟩

/-- Invert `SLe` on a cons in the first string: the second string starts with the same head. -/
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

/-- The element produced by interleaving `(b₀, σ)` and `(b₁, τ)`. -/
def mergeElem (σ : Str) (b₀ : Bool) (τ : Str) (b₁ : Bool) : C.Element :=
  shapeElem (mergeVal σ b₀ τ b₁).2 (mergeVal σ b₀ τ b₁).1

/-- **The monotonicity of interleaving.** If `(b₀, σ) ⊑ (b₀', σ')` and `(b₁, τ) ⊑ (b₁', τ')` then the
interleavings are `⊑`-ordered. The crux that makes `merge` approximable. -/
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

/-- `SLe` characterizes the element order on `shapeElem`. -/
theorem shapeElem_le_iff {b b' : Bool} {σ σ' : Str} :
    shapeElem b σ ≤ shapeElem b' σ' ↔ SLe b σ b' σ' := by
  cases b <;> cases b' <;>
    simp only [shapeElem_true, shapeElem_false, SLe, strElem_le_strElem_iff,
      strBot_le_strBot_iff, strBot_le_strElem_iff, true_and]
  · exact ⟨fun h => absurd h not_strElem_le_strBot, fun h => absurd h (by simp)⟩

/-- The element-order form of `mergeVal_SLe`. -/
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

/-- **Exercise 5.16 (Scott 1981, PRG-19).** The interleaving map `merge : C × C → C` with
`merge(εx, δy) = ε·δ·merge(x, y)`. Built directly as an approximable map: an input neighbourhood
`shape b₀ σ ∪ shape b₁ τ` relates to the neighbourhoods of `mergeElem σ b₀ τ b₁`. -/
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

/-- Two approximable maps out of `C` agree as soon as they agree on every finite element `σ⊥` and
`σ` (Exercise 2.8). This is the workhorse for the map equalities below. -/
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

/-- **The value of `merge` on a pair of finite elements.** `merge(⟨(b₀, σ), (b₁, τ)⟩) =
mergeElem σ b₀ τ b₁`. The analogue of `liftC_strBot`/`liftC_strElem` for the product. -/
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

/-- The diagonal value: interleaving `(s, σ)` with itself doubles. -/
theorem mergeVal_diag (s : Bool) (σ : Str) : mergeVal σ s σ s = (double σ, s) := by
  induction σ with
  | nil => rfl
  | cons a σ ih => simp [mergeVal_cons_cons, ih]

/-- On the diagonal `merge(⟨(s, σ), (s, σ)⟩)` doubles `σ`. -/
theorem mergeElem_diag (s : Bool) (σ : Str) : mergeElem σ s σ s = shapeElem s (double σ) := by
  simp [mergeElem, mergeVal_diag]

/-- **Exercise 5.16 (Scott 1981, PRG-19).** `merge(x, x) = d(x)` for all `x ∈ |C|` (the doubling map
of Example 4.4). -/
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

/-- **Exercise 5.16 (Scott 1981, PRG-19).** `neg ∘ neg = id` as approximable maps: it suffices to
check on the finite elements `σ⊥`, `σ`, where it is `flip ∘ flip = id`. -/
theorem negMap_comp_negMap : negMap.comp negMap = idMap C := by
  apply map_ext_C
  · intro σ
    rw [toElementMap_comp, negMap_strBot, negMap_strBot, flip_flip, toElementMap_idMap]
  · intro σ
    rw [toElementMap_comp, negMap_strElem, negMap_strElem, flip_flip, toElementMap_idMap]

/-- **Exercise 5.16 (Scott 1981, PRG-19).** `neg(neg(x)) = x` for all `x ∈ |C|`. -/
theorem negMap_negMap (x : C.Element) : negMap.toElementMap (negMap.toElementMap x) = x := by
  have h := negMap_comp_negMap
  rw [← toElementMap_comp, h, toElementMap_idMap]

/-- **Exercise 5.16 — the recursion for `neg`, case `0`.** `neg(0·x) = 1·neg(x)` as a map identity. -/
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

/-- **Exercise 5.16 — the recursion for `neg`, case `1`.** `neg(1·x) = 0·neg(x)` as a map identity. -/
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

/-- Two maps `C × C → C` agree as soon as they agree on every pair of finite elements. -/
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

/-- **Exercise 5.16 (Scott 1981, PRG-19).** The defining recursion of `merge`:
`merge(εx, δy) = ε·δ·merge(x, y)` for all `x, y ∈ |C|` and bits `ε, δ`. -/
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
set_option linter.unusedVariables false

theorem example_516 : And
  (And
    (And
      (And
        (And
          (∀ (ε δ : Bool)
            (x y :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap ε) x)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap δ) y)))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                (DomainTheory.NeighbourhoodSystems.Example44.consMap ε)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                  (DomainTheory.NeighbourhoodSystems.Example44.consMap δ)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C)
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                    (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C x y)))))
          (∀
            (x :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C x x))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                DomainTheory.NeighbourhoodSystems.Exercise516.dMap x)))
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C)))
      (∀
        (x :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
              DomainTheory.NeighbourhoodSystems.Exercise516.negMap x))
          x))
    (@Eq
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
        DomainTheory.NeighbourhoodSystems.Example44.C)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
        (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.false))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
        DomainTheory.NeighbourhoodSystems.Example44.C (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.true)
        DomainTheory.NeighbourhoodSystems.Exercise516.negMap)))
  (@Eq
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
      DomainTheory.NeighbourhoodSystems.Example44.C)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
      DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
      (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.true))
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
      DomainTheory.NeighbourhoodSystems.Example44.C (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.false)
      DomainTheory.NeighbourhoodSystems.Exercise516.negMap)) :=
  @And.intro
  (And
    (And
      (And
        (And
          (∀ (ε δ : Bool)
            (x y :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap ε) x)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap δ) y)))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                (DomainTheory.NeighbourhoodSystems.Example44.consMap ε)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                  (DomainTheory.NeighbourhoodSystems.Example44.consMap δ)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C)
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                    (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C x y)))))
          (∀
            (x :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C x x))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                DomainTheory.NeighbourhoodSystems.Exercise516.dMap x)))
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C)))
      (∀
        (x :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
              DomainTheory.NeighbourhoodSystems.Exercise516.negMap x))
          x))
    (@Eq
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
        DomainTheory.NeighbourhoodSystems.Example44.C)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
        (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.false))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
        DomainTheory.NeighbourhoodSystems.Example44.C (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.true)
        DomainTheory.NeighbourhoodSystems.Exercise516.negMap)))
  (@Eq
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
      DomainTheory.NeighbourhoodSystems.Example44.C)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
      DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
      (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.true))
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
      DomainTheory.NeighbourhoodSystems.Example44.C (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.false)
      DomainTheory.NeighbourhoodSystems.Exercise516.negMap))
  (@And.intro
    (And
      (And
        (And
          (∀ (ε δ : Bool)
            (x y :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap ε) x)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap δ) y)))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                (DomainTheory.NeighbourhoodSystems.Example44.consMap ε)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                  (DomainTheory.NeighbourhoodSystems.Example44.consMap δ)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C)
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                    (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C x y)))))
          (∀
            (x :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C x x))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                DomainTheory.NeighbourhoodSystems.Exercise516.dMap x)))
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C)))
      (∀
        (x :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
              DomainTheory.NeighbourhoodSystems.Exercise516.negMap x))
          x))
    (@Eq
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
        DomainTheory.NeighbourhoodSystems.Example44.C)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
        (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.false))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
        DomainTheory.NeighbourhoodSystems.Example44.C (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.true)
        DomainTheory.NeighbourhoodSystems.Exercise516.negMap))
    (@And.intro
      (And
        (And
          (∀ (ε δ : Bool)
            (x y :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap ε) x)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap δ) y)))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                (DomainTheory.NeighbourhoodSystems.Example44.consMap ε)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                  (DomainTheory.NeighbourhoodSystems.Example44.consMap δ)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C)
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                    (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C x y)))))
          (∀
            (x :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C x x))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                DomainTheory.NeighbourhoodSystems.Exercise516.dMap x)))
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C)))
      (∀
        (x :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
              DomainTheory.NeighbourhoodSystems.Exercise516.negMap x))
          x)
      (@And.intro
        (And
          (∀ (ε δ : Bool)
            (x y :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap ε) x)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap δ) y)))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                (DomainTheory.NeighbourhoodSystems.Example44.consMap ε)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                  (DomainTheory.NeighbourhoodSystems.Example44.consMap δ)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C)
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                    (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C x y)))))
          (∀
            (x :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C x x))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                DomainTheory.NeighbourhoodSystems.Exercise516.dMap x)))
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C))
        (@And.intro
          (∀ (ε δ : Bool)
            (x y :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap ε) x)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap δ) y)))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                (DomainTheory.NeighbourhoodSystems.Example44.consMap ε)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                  (DomainTheory.NeighbourhoodSystems.Example44.consMap δ)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C)
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                    (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C x y)))))
          (∀
            (x :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C x x))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                DomainTheory.NeighbourhoodSystems.Exercise516.dMap x))
          DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap_cons
          DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap_diag)
        DomainTheory.NeighbourhoodSystems.Exercise516.negMap_comp_negMap)
      DomainTheory.NeighbourhoodSystems.Exercise516.negMap_negMap)
    DomainTheory.NeighbourhoodSystems.Exercise516.neg_cons_false)
  DomainTheory.NeighbourhoodSystems.Exercise516.neg_cons_true
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- `tail(b(σ⊥)) = σ⊥`. -/
theorem tailMap_consMap_strBot (b : Bool) (σ : Str) :
    tailMap.toElementMap ((consMap b).toElementMap (strBot σ)) = strBot σ := by
  rw [consMap_strBot, tailMap_strBot]; rfl

/-- `tail(b(σ)) = σ`. -/
theorem tailMap_consMap_strElem (b : Bool) (σ : Str) :
    tailMap.toElementMap ((consMap b).toElementMap (strElem σ)) = strElem σ := by
  rw [consMap_strElem, tailMap_strElem]; rfl

end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- The Thue–Morse substitution applied letterwise: each bit `b` is replaced by `b (¬b)`. -/
def expand : Str → Str
  | [] => []
  | b :: σ => b :: (!b) :: expand σ

@[simp] theorem expand_nil : expand [] = [] := rfl

@[simp] theorem expand_cons (b : Bool) (σ : Str) : expand (b :: σ) = b :: (!b) :: expand σ := rfl

/-- The Thue–Morse bit-function: `tm n = ⊕(binary digits of n)`, the parity of the number of `1`s in
the binary expansion of `n` (Lambek's description). -/
def tm (n : ℕ) : Bool := (Nat.bits n).foldr xor false

/-- **Exercise 5.16 (the operator `Φ`).** `Φ(x) = 0·merge(neg x, tail x)` as an approximable map. -/
def tmOp : ApproximableMap C C :=
  (consMap false).comp (mergeMap.comp (paired negMap tailMap))

@[simp] theorem tm_zero : tm 0 = false := by simp [tm, Nat.zero_bits]

/-- The length-`n` Thue–Morse prefix `[tm 0, tm 1, …, tm (n-1)]`. -/
def tmList (n : ℕ) : Str := (List.range n).map tm

@[simp] theorem tmList_zero : tmList 0 = [] := rfl

/-- **Exercise 5.16 (Scott 1981, PRG-19).** Scott's Thue–Morse element `t = 0·merge(neg t, tail t)`,
the least fixed point of `Φ`. -/
def tElt : C.Element := tmOp.fixElement

/-- `σΣ* = Σ*` iff `σ = Λ`. -/
theorem cone_univ_iff {σ : Str} : cone σ = Set.univ ↔ σ = [] := by
  constructor
  · intro h
    exact List.prefix_nil.mp (mem_cone.mp (h ▸ Set.mem_univ ([] : Str)))
  · rintro rfl; exact cone_nil

/-- `expand` distributes over append (it is a monoid morphism `Σ* → Σ*`). -/
theorem expand_append (σ τ : Str) : expand (σ ++ τ) = expand σ ++ expand τ := by
  induction σ with
  | nil => rfl
  | cons b σ ih => simp [ih]

/-- Each approximant is below the least fixed point. -/
theorem iterElem_le_fixElement {α : Type*} {V : NeighborhoodSystem α} (f : ApproximableMap V V)
    (n : ℕ) : f.iterElem n ≤ f.fixElement := by
  rw [f.fixElement_eq_iSupDirected]
  intro Z hZ
  rw [mem_iSupDirected]
  exact ⟨n, hZ⟩

/-- A one-step unfolding of the iterated bottom element: `fⁿ⁺¹(⊥) = f(fⁿ(⊥))`. -/
theorem iterElem_succ {α : Type*} {V : NeighborhoodSystem α} (f : ApproximableMap V V) (n : ℕ) :
    f.iterElem (n + 1) = f.toElementMap (f.iterElem n) := by
  rw [iterElem_eq_iterate, iterElem_eq_iterate]
  exact Function.iterate_succ_apply' f.toElementMap n V.bot

/-- The base of the iterated bottom element: `f⁰(⊥) = ⊥`. -/
theorem iterElem_zero' {α : Type*} {V : NeighborhoodSystem α} (f : ApproximableMap V V) :
    f.iterElem 0 = V.bot := by
  rw [iterElem_eq_iterate, Function.iterate_zero_apply]

/-- Every iterate of `expand` from `[0]` starts with `0` (so `Φ` keeps acting as `expand`). -/
theorem iterate_expand_cons (k : ℕ) : ∃ ρ, (expand^[k] [false] : Str) = false :: ρ := by
  induction k with
  | zero => exact ⟨[], rfl⟩
  | succ k ih =>
    obtain ⟨ρ, hρ⟩ := ih
    exact ⟨true :: expand ρ, by rw [Function.iterate_succ_apply', hρ]; rfl⟩

/-- The second (total/partial-flag) component of an interleaving with a partial first input is always
`false`: a partial input keeps the output partial. -/
theorem mergeVal_snd_false : ∀ (σ τ : Str) (b₁ : Bool), (mergeVal σ false τ b₁).2 = false
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: σ, _ :: τ, b₁ => by simp only [mergeVal_cons_cons]; exact mergeVal_snd_false σ τ b₁

/-- `(strBot τ)` has the cone of `σ` as a neighbourhood iff `σ` is a prefix of `τ`. -/
theorem strBot_mem_cone {σ τ : Str} : (strBot τ).mem (cone σ) ↔ σ <+: τ := by
  rw [strBot, mem_principal]
  exact ⟨fun h => cone_subset_cone.mp h.2, fun h => ⟨memC_cone σ, cone_subset_cone.mpr h⟩⟩

/-- `⊥ = []⊥` in `C` (the cone of `Λ` is the master). -/
theorem strBot_nil : strBot [] = C.bot := by
  apply Element.ext
  intro Y
  rw [strBot, mem_principal, mem_bot, cone_nil, C_master]
  exact ⟨fun h => Set.Subset.antisymm (Set.subset_univ _) h.2,
    fun h => ⟨h ▸ C.master_mem, h ▸ Set.Subset.refl _⟩⟩

/-- **Exercise 5.16 — the defining unfolding.** `t = 0·merge(neg t, tail t)`. -/
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

/-- Thue–Morse prefixes are nested in the prefix order. -/
theorem tmList_prefix {n m : ℕ} (h : n ≤ m) : tmList n <+: tmList m := by
  induction m with
  | zero => rw [Nat.le_zero.mp h]
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with hlt | rfl
    · exact (ih (Nat.lt_succ_iff.mp hlt)).trans (by rw [tmList_succ]; exact List.prefix_append _ _)
    · exact List.prefix_rfl

/-- The value of `Φ` on a partial element `σ⊥` is `(0 · weave σ)⊥`, the leading `0` prepended to the
interleaving of `(flip σ)⊥` and `(tail σ)⊥`. -/
theorem tmOp_strBot (σ : Str) :
    tmOp.toElementMap (strBot σ)
      = strBot (false :: (mergeVal (flip σ) false σ.tail false).1) := by
  unfold tmOp
  rw [toElementMap_comp, toElementMap_comp, toElementMap_paired, negMap_strBot, tailMap_strBot,
    show (strBot (flip σ)) = shapeElem false (flip σ) from rfl,
    show (strBot σ.tail) = shapeElem false σ.tail from rfl, mergeMap_pair, mergeElem,
    mergeVal_snd_false, shapeElem_false, consMap_strBot]

/-- The even recurrence `tm (2n) = tm n` (appending a `0`-digit does not change the parity). -/
theorem tm_two_mul (n : ℕ) : tm (2 * n) = tm n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · simp only [tm, Nat.bit0_bits n (by omega : n ≠ 0), List.foldr_cons, Bool.false_xor]

/-- The odd recurrence `tm (2n+1) = ¬ tm n` (appending a `1`-digit flips the parity). -/
theorem tm_two_mul_add_one (n : ℕ) : tm (2 * n + 1) = !tm n := by
  simp only [tm, Nat.bit1_bits n, List.foldr_cons, Bool.true_xor]

/-- **The morphism step on prefixes.** `expand (tmList m) = tmList (2m)`: applying the Thue–Morse
morphism to a length-`m` prefix yields the length-`2m` prefix — this is exactly the even/odd parity
recurrence in disguise. -/
theorem expand_tmList (m : ℕ) : expand (tmList m) = tmList (2 * m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have key : tmList (2 * (m + 1)) = tmList (2 * m) ++ [tm m, !tm m] := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, tmList_succ, tmList_succ,
        tm_two_mul_add_one, tm_two_mul, List.append_assoc]
      rfl
    rw [tmList_succ, expand_append, ih, key, expand_cons, expand_nil]

/-- **The bridge.** The `k`-fold morphism iterate of `[0]` is the Thue–Morse parity prefix of length
`2ᵏ`: `expandᵏ[0] = tmList (2ᵏ)`. -/
theorem expand_iterate_eq (k : ℕ) : (expand^[k] [false] : Str) = tmList (2 ^ k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, expand_tmList, show 2 * 2 ^ k = 2 ^ (k + 1) by ring]

/-- The interleaving of `h :: flip ρ` with `ρ` (both starting after a common head `h`) is
`h :: expand ρ`. This is the heart of why `Φ` *is* the Thue–Morse morphism on the trajectory. -/
theorem weave_head : ∀ (h : Bool) (ρ : Str), (mergeVal (h :: flip ρ) false ρ false).1 = h :: expand ρ
  | h, [] => rfl
  | h, c :: ρ => by
    simp only [flip_cons, mergeVal_cons_cons, expand_cons]
    rw [weave_head (!c) ρ]

/-- **The Thue–Morse trajectory.** On a partial element whose string starts with `0`, `Φ` acts as the
Thue–Morse morphism `expand`. -/
theorem tmOp_strBot_expand (ρ : Str) :
    tmOp.toElementMap (strBot (false :: ρ)) = strBot (expand (false :: ρ)) := by
  rw [tmOp_strBot]
  simp only [flip_cons, List.tail_cons, expand_cons]
  rw [weave_head (!false) ρ]

/-- **Exercise 5.16 (the approximants).** The `(k+1)`-st approximant of the least fixed point is the
partial element of the `k`-fold Thue–Morse morphism iterate of `[0]`:
`Φᵏ⁺¹(⊥) = (expandᵏ[0])⊥`. -/
theorem iterElem_succ_eq (k : ℕ) :
    tmOp.iterElem (k + 1) = strBot (expand^[k] [false]) := by
  induction k with
  | zero =>
    rw [iterElem_succ, iterElem_zero', ← strBot_nil, tmOp_strBot]
    rfl
  | succ k ih =>
    obtain ⟨ρ, hρ⟩ := iterate_expand_cons k
    rw [iterElem_succ, ih, hρ, tmOp_strBot_expand, ← hρ, Function.iterate_succ_apply']

end

section
set_option linter.unusedVariables false

theorem example_516_thue_morse : And
  (∀ (k : Nat),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.iterElem DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.tmOp
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (DomainTheory.NeighbourhoodSystems.Example44.strBot
        (@Nat.iterate DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.Exercise516.expand k (@List.cons Bool Bool.false (@List.nil Bool)))))
  (@Eq
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.Example44.C)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
      DomainTheory.NeighbourhoodSystems.Example44.C (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.false)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
        (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
        DomainTheory.NeighbourhoodSystems.ExampleB.Str
        (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
          DomainTheory.NeighbourhoodSystems.Example44.C)
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
        (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
          DomainTheory.NeighbourhoodSystems.Example44.C
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap DomainTheory.NeighbourhoodSystems.Exercise516.tElt)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Exercise516.tailMap DomainTheory.NeighbourhoodSystems.Exercise516.tElt))))
    DomainTheory.NeighbourhoodSystems.Exercise516.tElt) :=
  @And.intro
  (∀ (k : Nat),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.iterElem DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.tmOp
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (DomainTheory.NeighbourhoodSystems.Example44.strBot
        (@Nat.iterate DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.Exercise516.expand k (@List.cons Bool Bool.false (@List.nil Bool)))))
  (@Eq
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.Example44.C)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
      DomainTheory.NeighbourhoodSystems.Example44.C (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.false)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
        (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
        DomainTheory.NeighbourhoodSystems.ExampleB.Str
        (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
          DomainTheory.NeighbourhoodSystems.Example44.C)
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
        (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
          DomainTheory.NeighbourhoodSystems.Example44.C
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap DomainTheory.NeighbourhoodSystems.Exercise516.tElt)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Exercise516.tailMap DomainTheory.NeighbourhoodSystems.Exercise516.tElt))))
    DomainTheory.NeighbourhoodSystems.Exercise516.tElt)
  DomainTheory.NeighbourhoodSystems.Exercise516.iterElem_succ_eq
  DomainTheory.NeighbourhoodSystems.Exercise516.tElt_unfold
end

section
open DomainTheory.NeighbourhoodSystems

/-- An **overlap** of period `p ≥ 1` at offset `i`: a factor of length `2p+1` with period `p`. -/
def Overlap (i p : ℕ) : Prop := 1 ≤ p ∧ ∀ k, k ≤ p → tm (i + k) = tm (i + p + k)
end

section
open DomainTheory.NeighbourhoodSystems
open Example44 ExampleB NeighborhoodSystem

/-- Positions differing by `|a|` inside `a ++ (a ++ a)` carry the same symbol, for indices `< 2|a|`
(the three copies of `a` are identical). -/
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

/-- The `j`-th bit of the length-`n` Thue–Morse prefix is `tm j`. -/
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

/-- An even-indexed symbol differs from its successor: `tm (2x) ≠ tm (2x+1)`. -/
theorem tm_two_mul_ne (x : ℕ) : tm (2 * x) ≠ tm (2 * x + 1) := by
  rw [tm_two_mul, tm_two_mul_add_one]
  cases tm x <;> simp

/-- `tm x = tm (x+1)` forces `x` to be **odd**: equal consecutive symbols only straddle a block
boundary `(2m+1, 2m+2)`, never a block `(2m, 2m+1)`. -/
theorem odd_of_consec_eq {x : ℕ} (h : tm x = tm (x + 1)) : Odd x := by
  rcases Nat.even_or_odd x with ⟨m, hm⟩ | hodd
  · exfalso; rw [hm, ← two_mul] at h; exact tm_two_mul_ne m h
  · exact hodd

/-- **No three consecutive equal symbols** (the period-`1` case): `¬ (tm j = tm (j+1) ∧
tm (j+1) = tm (j+2))`. If both held, `j` and `j+1` would both be odd. -/
theorem no_three_consec (j : ℕ) : ¬ (tm j = tm (j + 1) ∧ tm (j + 1) = tm (j + 2)) := by
  rintro ⟨h1, h2⟩
  have hj : Odd j := odd_of_consec_eq h1
  have hj1 : Odd (j + 1) := odd_of_consec_eq h2
  rcases hj with ⟨a, rfl⟩
  rcases hj1 with ⟨b, hb⟩
  omega

/-- **Overlap-freeness of the Thue–Morse sequence** (Scott 1981, PRG-19; Thue 1912). No overlap
exists at any offset and period. -/
theorem no_overlap (p : ℕ) : ∀ i, ¬ Overlap i p := by
  induction p using Nat.strong_induction_on with
  | _ p IH =>
    intro i hov
    obtain ⟨hp1, hrel⟩ := hov
    obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' p
    · -- Even period `p = 2q`: contract to a period-`q` overlap.
      subst hq
      have hq1 : 1 ≤ q := by omega
      obtain ⟨a, hi | hi⟩ := Nat.even_or_odd' i
      · -- `i = 2a`: even positions give `tm (a+c) = tm (a+q+c)`.
        refine IH q (by omega) a ⟨hq1, fun c hc => ?_⟩
        have hk : 2 * c ≤ 2 * q := by omega
        have := hrel (2 * c) hk
        rw [tm_of_eq_two_mul (show i + 2 * c = 2 * (a + c) by omega),
          tm_of_eq_two_mul (show i + 2 * q + 2 * c = 2 * (a + q + c) by omega)] at this
        exact this
      · -- `i = 2a+1`: odd positions give `tm (a+c) = tm (a+q+c)` after stripping the `¬`.
        refine IH q (by omega) a ⟨hq1, fun c hc => ?_⟩
        have hk : 2 * c ≤ 2 * q := by omega
        have := hrel (2 * c) hk
        rw [tm_of_eq_two_mul_add_one (show i + 2 * c = 2 * (a + c) + 1 by omega),
          tm_of_eq_two_mul_add_one (show i + 2 * q + 2 * c = 2 * (a + q + c) + 1 by omega)] at this
        exact Bool.not_inj this
    · -- Odd period `p = 2q+1`.
      subst hq
      rcases Nat.eq_zero_or_pos q with rfl | hq1
      · -- `p = 1`: three consecutive equal symbols.
        refine no_three_consec i ⟨?_, ?_⟩
        · have := hrel 0 (by omega); simpa using this
        · have := hrel 1 (by omega); simpa [show i + 1 + 1 = i + 2 by omega] using this
      · -- `p = 2q+1 ≥ 3`.
        obtain ⟨a, hi | hi⟩ := Nat.even_or_odd' i
        · -- `i = 2a`: relations at `k = 0,1,2,3` give a run of three equal symbols at `a+q`.
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
        · -- `i = 2a+1`.
          subst hi
          rcases Nat.eq_or_lt_of_le hq1 with hq2 | hq2
          · -- `q = 1`, i.e. `p = 3`: a direct contradiction from the four relations.
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
          · -- `q ≥ 2`, i.e. `p ≥ 5`: relations at `k = 1,2,3,4` give a run of three at `a+q+1`.
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

/-- **The Thue–Morse sequence is cube-free.** A cube of period `p ≥ 1` (the factor `a·a·a` with
`|a| = p`) is in particular an overlap, so none exists. -/
theorem no_cube (i p : ℕ) (hp : 1 ≤ p) :
    ¬ ∀ k, k < 2 * p → tm (i + k) = tm (i + p + k) := by
  intro hcube
  exact no_overlap p i ⟨hp, fun k hk => hcube k (by omega)⟩

end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- **Property (a), prefix form.** Every Thue–Morse parity prefix is a prefix of `t`:
`(tmList n)⊥ ⊑ t` for all `n`. -/
theorem tmList_le_tElt (n : ℕ) : strBot (tmList n) ≤ tElt := by
  have hpre : tmList n <+: expand^[n] [false] := by
    rw [expand_iterate_eq]; exact tmList_prefix (Nat.le_of_lt (Nat.lt_two_pow_self))
  calc strBot (tmList n) ≤ strBot (expand^[n] [false]) :=
        strBot_le_strBot_iff.mpr hpre
    _ = tmOp.iterElem (n + 1) := (iterElem_succ_eq n).symm
    _ ≤ tElt := iterElem_le_fixElement tmOp (n + 1)

/-- **Property (a), digit form.** The `n`-th digit of `t` is `tm n` (the parity of the binary digits
of `n`): the length-`(n+1)` prefix of `t` is `tmList n ++ [tm n]`. -/
theorem tElt_digit (n : ℕ) : strBot (tmList n ++ [tm n]) ≤ tElt := by
  have h := tmList_le_tElt (n + 1)
  rwa [tmList_succ] at h

/-- **Property (a) (Scott 1981, PRG-19; Lambek).** The finite-prefix characterization of `t`: a
string `σ` is a prefix of `t` **iff** it is the length-`σ.length` Thue–Morse parity prefix. Reading
off position `n`, the `n`-th digit of `t` is `tm n`, the parity of the binary digits of `n`. -/
theorem tElt_mem_cone_iff (σ : Str) : tElt.mem (cone σ) ↔ σ = tmList σ.length := by
  constructor
  · intro hσ
    rw [show tElt = tmOp.fixElement from rfl, tmOp.fixElement_eq_iSupDirected,
      mem_iSupDirected] at hσ
    obtain ⟨n, hn⟩ := hσ
    -- `σ` is a prefix of some Thue–Morse prefix `tmList N`.
    obtain ⟨N, hpre⟩ : ∃ N, σ <+: tmList N := by
      cases n with
      | zero =>
        rw [iterElem_zero', mem_bot, C_master, cone_univ_iff] at hn
        exact ⟨0, by rw [hn]; exact List.nil_prefix⟩
      | succ k =>
        rw [iterElem_succ_eq, strBot_mem_cone, expand_iterate_eq] at hn
        exact ⟨2 ^ k, hn⟩
    -- Both `σ` and `tmList σ.length` are the length-`σ.length` prefix of `tmList N`.
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

/-- **Exercise 5.16 (Scott 1981, PRG-19) — `t` is cube-free.** Scott's literal statement: `t` is not
of the form `u·a·a·a·v` for any finite prefix `u` and nonempty finite block `a`. (`v` is whatever
follows; we phrase "`u·a·a·a` is a prefix of `t`" as `(u·a·a·a)⊥ ⊑ t`.) -/
theorem tElt_cube_free (u a : Str) (ha : a ≠ []) :
    ¬ strBot (u ++ a ++ a ++ a) ≤ tElt := by
  intro hle
  -- `u·a·a·a` is a prefix of `t`, hence equals the Thue–Morse prefix of its length.
  have hmem : tElt.mem (cone (u ++ a ++ a ++ a)) :=
    hle _ (strBot_mem_cone.mpr List.prefix_rfl)
  have heq : u ++ a ++ a ++ a = tmList (u ++ a ++ a ++ a).length :=
    (tElt_mem_cone_iff _).mp hmem
  -- Read off a cube in `tm` at offset `|u|`, period `|a|`.
  set N := (u ++ a ++ a ++ a).length with hN
  have hlen : N = u.length + 3 * a.length := by simp only [hN, List.length_append]; omega
  have hp : 1 ≤ a.length := by
    cases a with
    | nil => exact (ha rfl).elim
    | cons _ _ => simp
  refine no_cube u.length a.length hp (fun k hk => ?_)
  -- Both `tm (|u|+k)` and `tm (|u|+|a|+k)` read the same bit of `u·a·a·a`.
  have hk3 : u.length + k < N := by omega
  have hk3' : u.length + a.length + k < N := by omega
  have e1 : (tmList N)[u.length + k]? = some (tm (u.length + k)) := tmList_getElem? hk3
  have e2 : (tmList N)[u.length + a.length + k]? = some (tm (u.length + a.length + k)) :=
    tmList_getElem? hk3'
  -- Rewrite the prefix as `u ++ (a ++ (a ++ a))` and strip `u`.
  have hassoc : u ++ a ++ a ++ a = u ++ (a ++ (a ++ a)) := by
    simp [List.append_assoc]
  rw [← heq, hassoc] at e1 e2
  rw [List.getElem?_append_right (by omega : u.length ≤ u.length + k),
    show u.length + k - u.length = k by omega] at e1
  rw [List.getElem?_append_right (by omega : u.length ≤ u.length + a.length + k),
    show u.length + a.length + k - u.length = k + a.length by omega] at e2
  -- Period: `(a++(a++a))[k]? = (a++(a++a))[k+|a|]?`.
  have hper := append_three_period a k (by omega)
  have : some (tm (u.length + k)) = some (tm (u.length + a.length + k)) := by
    rw [← e1, hper, e2]
  exact Option.some.inj this
end

section
set_option linter.unusedVariables false

theorem example_516_overlap : ∀ (u a : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
  @Ne DomainTheory.NeighbourhoodSystems.ExampleB.Str a (@List.nil Bool) →
    Not
      (@LE.le
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.Example44.C)
        (@Preorder.toLE
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@PartialOrder.toPreorder
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)))
        (DomainTheory.NeighbourhoodSystems.Example44.strBot
          (@HAppend.hAppend DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            (@instHAppendOfAppend DomainTheory.NeighbourhoodSystems.ExampleB.Str (@List.instAppend Bool))
            (@HAppend.hAppend DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (@instHAppendOfAppend DomainTheory.NeighbourhoodSystems.ExampleB.Str (@List.instAppend Bool))
              (@HAppend.hAppend DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@instHAppendOfAppend DomainTheory.NeighbourhoodSystems.ExampleB.Str (@List.instAppend Bool)) u a)
              a)
            a))
        DomainTheory.NeighbourhoodSystems.Exercise516.tElt) :=
  DomainTheory.NeighbourhoodSystems.Exercise516.tElt_cube_free
end

end DomainTheory.NeighbourhoodSystems.Exercise516
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The **left-hand side** `λx. !y. τ(x, y)` of Proposition 5.4: `fix ∘ curry(τ)`. -/
def pfix (τ : ApproximableMap (prod V V) V) : ApproximableMap V V :=
  (fixMap V).comp (curry τ)

/-- The **operator** `λg. λx. τ(x, g(x))` of Proposition 5.4, as an approximable endomap of the
function space `(𝒟 → 𝒟)`: `recOp τ := curry(τ ∘ ⟨p₁, eval⟩)`. -/
def recOp (τ : ApproximableMap (prod V V) V) : ApproximableMap (funSpace V V) (funSpace V V) :=
  curry (τ.comp (paired (proj₁ (funSpace V V) V) (evalMap V V)))

/-- The section `y ↦ τ(x, y)` of `τ : 𝒟 × 𝒟 → 𝒟` at a fixed `x`, as an approximable endomap of
`𝒟` (the curried `τ` applied to `x`). -/
def section₂ (τ : ApproximableMap (prod V V) V) (x : V.Element) : ApproximableMap V V :=
  toApproxMap ((curry τ).toElementMap x)

/-- `pfix τ (x) = !y. τ(x, y)`, the least fixed point of the section at `x`. -/
theorem pfix_apply (τ : ApproximableMap (prod V V) V) (x : V.Element) :
    (pfix τ).toElementMap x = (section₂ τ x).fixElement := by
  rw [pfix, toElementMap_comp, fixMap_toElementMap, section₂]

/-- `recOp τ (g) (x) = τ(x, g(x))`. -/
theorem recOp_apply (τ : ApproximableMap (prod V V) V) (φ : (funSpace V V).Element) (x : V.Element) :
    (toApproxMap ((recOp τ).toElementMap φ)).toElementMap x
      = τ.toElementMap (pair x ((toApproxMap φ).toElementMap x)) := by
  rw [recOp, toElementMap_curry_apply, toElementMap_comp, toElementMap_paired,
    toElementMap_proj₁, snd_pair, evalMap_apply]

theorem section₂_apply (τ : ApproximableMap (prod V V) V) (x y : V.Element) :
    (section₂ τ x).toElementMap y = τ.toElementMap (pair x y) := by
  rw [section₂, toElementMap_curry_apply]

/-- `pfix τ` is a fixed point of `recOp τ` (pointwise: `τ(x, pfix τ x) = pfix τ x`). -/
theorem pfix_isFixed (τ : ApproximableMap (prod V V) V) (x : V.Element) :
    τ.toElementMap (pair x ((pfix τ).toElementMap x)) = (pfix τ).toElementMap x := by
  rw [pfix_apply, ← section₂_apply, toElementMap_fixElement]

end ApproximableMap
end
end DomainTheory.NeighbourhoodSystems
end

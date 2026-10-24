module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_19

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The finite intersection `⋂_{i < n} Xᵢ` of the first `n` terms of a sequence of
/- concordance: source L131 FACTOID 1.1a empty intersection is delta -/
neighbourhoods, defined by Scott's recursive convention (**Factoid 1.1a / 1.1b**):

* `n = 0` : the empty intersection is `Δ` (`master`);
* `n + 1` : `(⋂_{i < n} Xᵢ) ∩ Xₙ`.

(See `interUpTo_zero` and `interUpTo_succ` for the two defining equations as lemmas.) -/
def interUpTo (V : NeighborhoodSystem α) (X : ℕ → Set α) : ℕ → Set α
  | 0 => V.master
  | (n + 1) => interUpTo V X n ∩ X n

/-- **Factoid 1.1a.** The intersection of the empty sequence of neighbourhoods is `Δ`:
`⋂_{i < 0} Xᵢ = Δ`. -/
@[simp] theorem interUpTo_zero (X : ℕ → Set α) : V.interUpTo X 0 = V.master := rfl

/- concordance: source L135 FACTOID 1.1b recursive finite intersection -/
/-- **Factoid 1.1b.** The intersection of the first `n + 1` neighbourhoods peels off the
last factor: `⋂_{i < n+1} Xᵢ = (⋂_{i < n} Xᵢ) ∩ Xₙ`. -/
@[simp] theorem interUpTo_succ (X : ℕ → Set α) (n : ℕ) :
    V.interUpTo X (n + 1) = V.interUpTo X n ∩ X n := rfl

/-- A finite sequence `X₀, …, Xₙ₋₁` of neighbourhoods is *consistent in* `𝒟` when it has a
common lower bound inside `𝒟`: some `Z ∈ 𝒟` contained in the intersection `⋂_{i < n} Xᵢ`
(equivalently, contained in every `Xⱼ`, `j < n`). This is Scott's notion of consistency,
generalized from pairs to finite sequences. -/
def Consistent (X : ℕ → Set α) (n : ℕ) : Prop :=
  ∃ Z, V.mem Z ∧ Z ⊆ V.interUpTo X n

/-- Filter-inclusion order on elements (Scott's approximation order, Definition 1.8).
Named so Palomar can lock the `PartialOrder` relation without inlining it. -/
def element_le (x y : V.Element) : Prop :=
  ∀ X, x.mem X → y.mem X

/-- Reflexivity of the filter-inclusion order. Named so Palomar can lock the
`PartialOrder` instance without a generated `._proof_N`. -/
theorem element_le_refl (x : V.Element) : ∀ X, x.mem X → x.mem X :=
  fun _ h => h

/-- Transitivity of the filter-inclusion order. -/
theorem element_le_trans (x y z : V.Element)
    (hxy : ∀ X, x.mem X → y.mem X) (hyz : ∀ X, y.mem X → z.mem X) :
    ∀ X, x.mem X → z.mem X :=
  fun X h => hyz X (hxy X h)

/-- Two elements with the same membership predicate are equal (the remaining fields are `Prop`s). -/
theorem Element.ext {x y : V.Element} (h : ∀ X, x.mem X ↔ y.mem X) : x = y := by
  rcases x with ⟨xmem, _, _, _, _⟩
  rcases y with ⟨ymem, _, _, _, _⟩
  have hmem : xmem = ymem := funext fun X => propext (h X)
  subst hmem
  rfl

/-- Antisymmetry of the filter-inclusion order. -/
theorem element_le_antisymm (x y : V.Element)
    (hxy : ∀ X, x.mem X → y.mem X) (hyx : ∀ X, y.mem X → x.mem X) :
    x = y :=
  @Element.ext α V x y fun X => ⟨hxy X, hyx X⟩

/-- Elements are ordered by inclusion of their membership predicates (Scott's approximation
order, Definition 1.8). -/
instance : PartialOrder V.Element where
  le := element_le V
  le_refl := element_le_refl V
  le_trans := element_le_trans V
  le_antisymm := element_le_antisymm V

/-- Two sequences of neighbourhoods are **equivalent** ("each goes equally deep as the other"):
for every `Yₘ` some `Xₙ ⊆ Yₘ`, and for every `Xₙ` some `Yₘ ⊆ Xₙ`. -/
def SeqEquiv (X Y : ℕ → Set α) : Prop :=
  (∀ m, ∃ n, X n ⊆ Y m) ∧ (∀ n, ∃ m, Y m ⊆ X n)

/-- The **limit family** of a sequence of neighbourhoods (Scott, the prose before Definition
1.6): `x = {Z ∈ 𝒟 ∣ Xₙ ⊆ Z for some n}` — the family of all neighbourhoods eventually reached
by `⟨Xₙ⟩`. This is the construction Scott uses to motivate the (ideal) elements of `|𝒟|`. -/
def limitFamily (X : ℕ → Set α) : Set (Set α) := {Z | V.mem Z ∧ ∃ n, X n ⊆ Z}
end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

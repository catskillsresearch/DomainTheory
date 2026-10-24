module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_7
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Examples_1_2_1_5_revisited

@[expose] public section

/- concordance: source L282 FACTOID 1.8a1 bottom element -/

section
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

/- concordance: source L282 FACTOID 1.8a2 bottom is least -/
/-- **Factoid 1.8a (Scott 1981, PRG-19).** "The element that approximates all others, `{Δ}`,
is called `⊥`": `⊥` is the least element of `|𝒟|`, `⊥ ⊑ x` for every `x`.

Given `Y ∈ ⊥`, i.e. `Y = Δ`, membership `Δ ∈ x` is filter condition (i) (`x.master_mem`). -/
theorem bot_le (x : V.Element) : V.bot ≤ x := by
  intro Y hY
  rw [mem_bot] at hY
  subst hY
  exact x.master_mem

/-- **Factoid 1.8a, packaged.** `⊥` is an `OrderBot` for the approximation order, so the `⊥`
notation refers to `{Δ}`. Constructive (`bot_le` is `[propext, Quot.sound]`). -/
instance : OrderBot V.Element where
  bot := V.bot
  bot_le := V.bot_le

/- concordance: source L284 FACTOID 1.8b finite filters are principal -/
/- concordance: source L284 EXAMPLES 1.2–1.5 finite examples revisited -/
/-- **Factoid 1.8b (Scott 1981, PRG-19) — "Examples 1.2–1.5 revisited".** "Any explicitly given
filter `x` is principal … the minimal `X ∈ x` tells us all we need to know." Stated honestly: if
the filter `x` has a `⊆`-minimum member `X` (one contained in every member of `x`), then `x` is
exactly the principal filter `↑X`. In a *finite* system every filter has such a minimum (the
intersection of its finitely many members, itself in `x` by closure), so every element is
principal; that finiteness step is the only classical ingredient and is left implicit here — this
constructive core captures the content.

`⊆`: any `Z ∈ x` satisfies `X ⊆ Z` by minimality, so `Z ∈ ↑X`. `⊇`: `Z ∈ ↑X` means `Z ∈ 𝒟` and
`X ⊆ Z`, so `Z ∈ x` by upward closure from `X ∈ x`. -/
theorem eq_principal_of_isMin (x : V.Element) {X : Set α} (hX : x.mem X)
    (hmin : ∀ Y, x.mem Y → X ⊆ Y) : x = V.principal (x.sub hX) := by
  apply Element.ext
  intro Z
  constructor
  · intro hZ
    exact ⟨x.sub hZ, hmin Z hZ⟩
  · rintro ⟨hZmem, hXZ⟩
    exact x.up_mem hX hZmem hXZ
end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.ExampleB
section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/- concordance: source L317 FACTOID 1.8d union of finite approximations -/
/-- **Factoid (Scott 1981, PRG-19).** "`x = ⋃ₙ σₙ⊥`": every `x ∈ |B|` is the union of the finite
elements `σ⊥` whose generating cone `σΣ*` lies in `x`. In membership form, a neighbourhood `Z`
belongs to `x` iff `Z` lies in some `σ⊥ = ↑(σΣ*)` with `σΣ* ∈ x`.

This is the concrete "an element is uniquely determined by its finite approximations" in `|B|`
(`Basic.eq_iUnion_principal` specialized to `B`, where every neighbourhood is a cone). The further
arrangement of the `σ` into a single increasing chain `σ₀ ⪯ σ₁ ⪯ …` requires choice/enumeration and
is left to Scott's prose. -/
theorem mem_iff_exists_sigmaBot (x : B.Element) {Z : Set Str} :
    x.mem Z ↔ ∃ σ, x.mem (cone σ) ∧ (sigmaBot σ).mem Z := by
  constructor
  · intro hZ
    obtain ⟨σ, rfl⟩ := x.sub hZ
    exact ⟨σ, hZ, x.sub hZ, subset_rfl⟩
  · rintro ⟨σ, hcone, hZmem, hsub⟩
    exact x.up_mem hcone hZmem hsub

/-- **Prepending is associative.** `σ(τX) = (στ)X`: prepending `σ` after `τ` is the same as
prepending the concatenation `σ ++ τ` in one step (used to compose `sigmaElt`, `Exercise216`). -/
theorem prepend_append (σ τ : Str) (X : Set Str) :
    prepend σ (prepend τ X) = prepend (σ ++ τ) X := by
  ext w
  simp only [mem_prepend]
  constructor
  · rintro ⟨ρ, ⟨ρ', hρ', rfl⟩, rfl⟩
    exact ⟨ρ', hρ', by rw [List.append_assoc]⟩
  · rintro ⟨ρ, hρ, rfl⟩
    exact ⟨τ ++ ρ, ⟨ρ, hρ, rfl⟩, by rw [List.append_assoc]⟩

/-- **Prepending is monotone.** `X' ⊆ X → σX' ⊆ σX` (Exercise 2.16's `sigmaMap` uses this for
its `mono` clause; `sigmaElt_append` uses it to transport the up-closure through composition). -/
theorem prepend_mono (σ : Str) {X X' : Set Str} (h : X' ⊆ X) : prepend σ X' ⊆ prepend σ X := by
  rintro w ⟨τ, hτ, rfl⟩
  exact ⟨τ, h hτ, rfl⟩

/-- `σΣ* = σ·Σ*`: prepending `σ` to the whole space recovers the cone of `σ`. -/
theorem prepend_univ (σ : Str) : prepend σ Set.univ = cone σ := by
  ext w
  simp only [mem_prepend, Set.mem_univ, true_and, mem_cone]
  constructor
  · rintro ⟨τ, rfl⟩
    exact List.prefix_append σ τ
  · rintro ⟨t, ht⟩
    exact ⟨t, ht.symm⟩

/- concordance: source L312 FACTOID 1.8c prefix order -/
/-- **Factoid (Scott 1981, PRG-19).** "`σ₀⊥ ⊆ σ₁⊥` if and only if `σ₀` is an *initial segment* of
the sequence `σ₁`." The approximation order on finite elements is exactly the prefix order:
`σ₀⊥ ⊑ σ₁⊥ ↔ σ₀ <+: σ₁`. (Via `principal_le_iff` — reversal — composed with `cone_subset_cone` —
reversal again — which cancel to give the prefix order directly.) -/
theorem sigmaBot_le_iff (σ₀ σ₁ : Str) :
    sigmaBot σ₀ ≤ sigmaBot σ₁ ↔ σ₀ <+: σ₁ := by
  rw [sigmaBot, sigmaBot, B.principal_le_iff, cone_subset_cone]

/-- **`σ` and `τ` prepend in sequence, like concatenation.** `(στ)x = σ(τx)`: applying the
prefix `σ ++ τ` in one step agrees with applying `τ` first and then `σ`. (Used in Exercise 2.16's
second half — the uniqueness of the parity map — to unfold `f(σ₁σ₂ … σₙx)` one token at a time.) -/
theorem sigmaElt_append (σ τ : Str) (x : B.Element) :
    sigmaElt (σ ++ τ) x = sigmaElt σ (sigmaElt τ x) := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨hY, X, hX, hsub⟩
    refine ⟨hY, prepend τ X, ⟨memB_prepend τ (x.sub hX), X, hX, subset_rfl⟩, ?_⟩
    rw [prepend_append]; exact hsub
  · rintro ⟨hY, X, ⟨_, X', hX', hsub'⟩, hsub⟩
    refine ⟨hY, X', hX', ?_⟩
    rw [← prepend_append]
    exact (prepend_mono σ hsub').trans hsub

/-- **`σ⊥` really is `σ` applied to `⊥`.** `sigmaElt σ ⊥ = sigmaBot σ`, justifying the `σ⊥`
notation: applying `σ` to the least element produces the finite element `↑(σΣ*)`. -/
theorem sigmaElt_bot (σ : Str) : sigmaElt σ B.bot = sigmaBot σ := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨hY, X, hX, hsub⟩
    rw [B.mem_bot] at hX
    subst hX
    rw [B_master, prepend_univ] at hsub
    exact ⟨hY, hsub⟩
  · rintro ⟨hY, hcone⟩
    refine ⟨hY, B.master, B.mem_bot.mpr rfl, ?_⟩
    rw [B_master, prepend_univ]
    exact hcone

/-- **Prepending the empty prefix fixes every element.** `Λx = x` — the identity case of
`sigmaElt`, matching `prepend_nil` on neighbourhoods. -/
theorem sigmaElt_nil (x : B.Element) : sigmaElt [] x = x := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨hY, X, hX, hsub⟩
    rw [prepend_nil] at hsub
    exact x.up_mem hX hY hsub
  · intro hY
    exact ⟨x.sub hY, Y, hY, by rw [prepend_nil]⟩
end

end DomainTheory.NeighbourhoodSystems.ExampleB
end

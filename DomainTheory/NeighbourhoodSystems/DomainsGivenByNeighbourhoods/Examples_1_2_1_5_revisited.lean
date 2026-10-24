module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example_1_2
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example_1_3
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example_1_4
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example_1_5

@[expose] public section

/- concordance: source L284 EXAMPLES 1.2–1.5 finite examples revisited -/

section
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Examples 1.2–1.5 revisited.** A filter with a `⊆`-least neighbourhood `X` is the principal
filter `↑X`: the least neighbourhood determines the element. -/
theorem eq_principal_of_minimum (x : V.Element) {X : Set α} (hX : x.mem X)
    (hmin : ∀ Y, x.mem Y → X ⊆ Y) : x = V.principal (x.sub hX) := by
  apply Element.ext
  intro Z
  constructor
  · intro hZ
    exact ⟨x.sub hZ, hmin Z hZ⟩
  · rintro ⟨hZ, hXZ⟩
    exact x.up_mem hX hZ hXZ

/-- On a finite token set every element has a `⊆`-least neighbourhood: descend on cardinality
from `Δ`, and close the least candidate under intersection with an arbitrary member. -/
theorem exists_minimum_of_fintype [Fintype α] (x : V.Element) :
    ∃ X, x.mem X ∧ ∀ Y, x.mem Y → X ⊆ Y := by
  classical
  suffices aux : ∀ n (A : Set α), A.ncard = n → x.mem A →
      ∃ X, x.mem X ∧ X ⊆ A ∧ ∀ Y, x.mem Y → Y ⊆ A → X ⊆ Y from by
    obtain ⟨X, hX, _, hmin⟩ := aux V.master.ncard V.master rfl x.master_mem
    exact ⟨X, hX, fun Y hY => hmin Y hY (V.sub_master (x.sub hY))⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A hn hA
    by_cases hleast : ∀ Y, x.mem Y → Y ⊆ A → A ⊆ Y
    · exact ⟨A, hA, subset_rfl, hleast⟩
    · push Not at hleast
      obtain ⟨Y, hY, hYA, hAY⟩ := hleast
      have hss : Y ⊂ A := ⟨hYA, hAY⟩
      have hlt : Y.ncard < n := by
        rw [← hn]
        exact Set.ncard_lt_ncard hss
      obtain ⟨X, hX, hXsub, hmin⟩ := ih Y.ncard hlt Y rfl hY
      refine ⟨X, hX, hXsub.trans hYA, ?_⟩
      intro Z hZ hZA
      have hcap : x.mem (Z ∩ Y) := x.inter_mem hZ hY
      exact (hmin (Z ∩ Y) hcap Set.inter_subset_right).trans Set.inter_subset_left

/-- **Examples 1.2–1.5 revisited.** "The examples as given were all finite, so any explicitly
given filter `x` is principal … the minimal `X ∈ x` tells us all we need to know." -/
theorem element_eq_principal_of_fintype [Fintype α] (x : V.Element) :
    ∃ X, ∃ hX : V.mem X, x = V.principal hX := by
  obtain ⟨X, hX, hmin⟩ := V.exists_minimum_of_fintype x
  exact ⟨X, x.sub hX, V.eq_principal_of_minimum x hX hmin⟩

/-- **Examples 1.2–1.5 revisited.** The order reverses: a smaller neighbourhood determines a
better element. `X ⊆ Y` means `↑Y ⊑ ↑X`. -/
theorem smaller_neighbourhood_le {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) :
    V.principal hY ≤ V.principal hX ↔ X ⊆ Y := by
  constructor
  · intro h
    exact (h Y ⟨hY, subset_rfl⟩).2
  · intro hXY Z hZ
    exact ⟨hZ.1, hXY.trans hZ.2⟩
end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Example12
/-- Every element of Example 1.2 is the principal filter of its least neighbourhood. -/
theorem element_eq_principal (x : neighborhoodSystem.Element) :
    ∃ X, ∃ hX : neighborhoodSystem.mem X, x = neighborhoodSystem.principal hX :=
  NeighborhoodSystem.element_eq_principal_of_fintype neighborhoodSystem x

end DomainTheory.NeighbourhoodSystems.Example12
namespace DomainTheory.NeighbourhoodSystems.Example13
/-- Every element of Example 1.3 is the principal filter of its least neighbourhood. -/
theorem element_eq_principal (x : neighborhoodSystem.Element) :
    ∃ X, ∃ hX : neighborhoodSystem.mem X, x = neighborhoodSystem.principal hX :=
  NeighborhoodSystem.element_eq_principal_of_fintype neighborhoodSystem x

end DomainTheory.NeighbourhoodSystems.Example13
namespace DomainTheory.NeighbourhoodSystems.Example14
/-- Every element of the finite tree (Example 1.4) is the principal filter of its least
neighbourhood. The infinite system `B` below is a different example. -/
theorem element_eq_principal (x : neighborhoodSystem.Element) :
    ∃ X, ∃ hX : neighborhoodSystem.mem X, x = neighborhoodSystem.principal hX :=
  NeighborhoodSystem.element_eq_principal_of_fintype neighborhoodSystem x

end DomainTheory.NeighbourhoodSystems.Example14
namespace DomainTheory.NeighbourhoodSystems.Example15
/-- Every element of Example 1.5 is the principal filter of its least neighbourhood. -/
theorem element_eq_principal (x : neighborhoodSystem.Element) :
    ∃ X, ∃ hX : neighborhoodSystem.mem X, x = neighborhoodSystem.principal hX :=
  NeighborhoodSystem.element_eq_principal_of_fintype neighborhoodSystem x

end DomainTheory.NeighbourhoodSystems.Example15
namespace DomainTheory.NeighbourhoodSystems.ExampleB
section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- The token type `Σ* = List Bool` (finite binary strings); `Λ = []`. -/
abbrev Str := List Bool

/-- The neighbourhood `σΣ*`: all *extensions* of `σ` (sequences with `σ` as an initial segment). -/
def cone (σ : Str) : Set Str := {w | σ <+: w}

@[simp] theorem mem_cone {σ w : Str} : w ∈ cone σ ↔ σ <+: w := Iff.rfl

/-- `ΛΣ* = Σ*`: the cone of the empty string is everything (Scott's `Δ`). -/
theorem cone_nil : cone [] = Set.univ := by
  ext w; simp [cone]

/-- **Cones reverse the prefix order.** `σΣ* ⊆ τΣ*` iff `τ` is an initial segment of `σ`: a longer
prefix carves out a *smaller* cone. (`→` tests at `σ ∈ σΣ*`; `←` is transitivity of `<+:`.) -/
theorem cone_subset_cone {σ τ : Str} : cone σ ⊆ cone τ ↔ τ <+: σ := by
  constructor
  · intro h
    exact h (show σ ∈ cone σ from List.prefix_rfl)
  · intro hτσ w hw
    exact hτσ.trans hw

/-- **Prefix trichotomy for cones.** Any two cones are nested-or-disjoint: either one contains the
other, or they are disjoint (incomparable prefixes have no common extension). Choice-free: the
prefix relation on `List Bool` is decidable. -/
theorem cone_trichotomy (σ τ : Str) :
    cone σ ⊆ cone τ ∨ cone τ ⊆ cone σ ∨ cone σ ∩ cone τ = ∅ :=
  if hστ : σ <+: τ then Or.inr (Or.inl (cone_subset_cone.mpr hστ))
  else if hτσ : τ <+: σ then Or.inl (cone_subset_cone.mpr hτσ)
  else Or.inr (Or.inr (by
    ext w
    simp only [Set.mem_inter_iff, mem_cone, Set.mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
    · exact hστ h
    · exact hτσ h))

/-- Membership in Scott's binary neighbourhood system `B`: `X ∈ B` iff `X = σΣ*` for some `σ`. -/
def memB (X : Set Str) : Prop := ∃ σ, X = cone σ

/-- **Exercise ("`B` is a neighbourhood system").** The family `B = {σΣ* ∣ σ ∈ Σ*}` is pairwise
nested-or-disjoint, by `cone_trichotomy`. -/
theorem nestedOrDisjoint : NestedOrDisjoint memB := by
  rintro X Y ⟨σ, rfl⟩ ⟨τ, rfl⟩
  exact cone_trichotomy σ τ

/-- **Examples 1.2–1.5 revisited — the infinite form of Example 1.4.**
Scott's `B` on `Δ = Σ*`. This is a new system: Example 1.4 remains the finite tree of sequences
of length at most 2. -/
def B : NeighborhoodSystem Str :=
  NeighborhoodSystem.ofNestedOrDisjoint memB Set.univ
    ⟨[], Set.mem_univ _⟩ ⟨[], cone_nil.symm⟩ nestedOrDisjoint
    (fun _ => Set.subset_univ _)

@[simp] theorem B_mem {X : Set Str} : B.mem X ↔ memB X := Iff.rfl

@[simp] theorem B_master : B.master = Set.univ := rfl

/-- Every cone is a neighbourhood of `B`. -/
theorem memB_cone (σ : Str) : B.mem (cone σ) := ⟨σ, rfl⟩

/-- Scott's `σX = {στ ∣ τ ∈ X}` (prepend the prefix `σ` to every member of `X`). -/
def prepend (σ : Str) (X : Set Str) : Set Str := {w | ∃ τ, τ ∈ X ∧ w = σ ++ τ}

@[simp] theorem mem_prepend {σ : Str} {X : Set Str} {w : Str} :
    w ∈ prepend σ X ↔ ∃ τ, τ ∈ X ∧ w = σ ++ τ := Iff.rfl

/-- **`σ(τΣ*) = (στ)Σ*`.** Prepending `σ` to a cone yields the cone of the concatenation — this is
why `σx` lands back in `B` and why `σ⊥` is again a finite element. -/
theorem prepend_cone (σ ρ : Str) : prepend σ (cone ρ) = cone (σ ++ ρ) := by
  ext w
  simp only [mem_prepend, mem_cone]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact (List.prefix_append_right_inj σ).mpr hτ
  · rintro ⟨t, ht⟩
    exact ⟨ρ ++ t, List.prefix_append ρ t, by rw [← ht, List.append_assoc]⟩

/-- Prepending preserves membership in `B` (`σ` applied to a cone is a cone). -/
theorem memB_prepend (σ : Str) {X : Set Str} (hX : B.mem X) : B.mem (prepend σ X) := by
  obtain ⟨ρ, rfl⟩ := hX
  exact ⟨σ ++ ρ, prepend_cone σ ρ⟩

@[simp] theorem prepend_nil (X : Set Str) : prepend [] X = X := by
  ext w; simp [mem_prepend]

/-- **`σ⊥`, a finite element of `|B|`.** The principal filter `↑(σΣ*)` of the cone of `σ`; its
minimal neighbourhood is `σΔ = σΣ*` (Scott). These are exactly the finite elements of `|B|`. -/
def sigmaBot (σ : Str) : B.Element := B.principal (memB_cone σ)

/-- **Exercise (`σx ∈ |B|`).** For `x ∈ |B|` and `σ ∈ Σ*`, Scott's
`σx = {Y ∣ σX ⊆ Y for some X ∈ x}` is again an element of `|B|`.

The filter laws: `master` uses `X = Δ ∈ x` (`σΔ ⊆ Δ` trivially); `inter` takes `X₁ ∩ X₂ ∈ x` and
the consistency witness `σ(X₁∩X₂)`, which is a *cone* (hence in `B`, by `memB_prepend`) contained in
both `Y₁` and `Y₂`; `up` reuses the same `X`. -/
def sigmaElt (σ : Str) (x : B.Element) : B.Element where
  mem Y := B.mem Y ∧ ∃ X, x.mem X ∧ prepend σ X ⊆ Y
  sub h := h.1
  master_mem := ⟨B.master_mem, B.master, x.master_mem, Set.subset_univ _⟩
  inter_mem := by
    intro Y₁ Y₂ h1 h2
    obtain ⟨hY₁, X₁, hX₁, hsub₁⟩ := h1
    obtain ⟨hY₂, X₂, hX₂, hsub₂⟩ := h2
    have hXinter : x.mem (X₁ ∩ X₂) := x.inter_mem hX₁ hX₂
    have hsub : prepend σ (X₁ ∩ X₂) ⊆ Y₁ ∩ Y₂ := by
      rintro w ⟨τ, ⟨hτ₁, hτ₂⟩, rfl⟩
      exact ⟨hsub₁ ⟨τ, hτ₁, rfl⟩, hsub₂ ⟨τ, hτ₂, rfl⟩⟩
    have hZmem : B.mem (prepend σ (X₁ ∩ X₂)) := memB_prepend σ (x.sub hXinter)
    exact ⟨B.inter_mem hY₁ hY₂ hZmem hsub, X₁ ∩ X₂, hXinter, hsub⟩
  up_mem := by
    intro X Y hX hY hXY
    obtain ⟨_, X', hX', hsub'⟩ := hX
    exact ⟨hY, X', hX', hsub'.trans hXY⟩

/-- **Cones are one-one in the prefix.** `cone σ = cone τ ⟹ σ = τ`: from the two inclusions we get
`τ <+: σ` and `σ <+: τ`, and a prefix-antisymmetry (equal lengths) finishes. Used by the approximable
maps `B → T` / `B → B` (Examples 2.3, 2.4) to read off the unique generating prefix of a cone. -/
theorem cone_injective {σ τ : Str} (h : cone σ = cone τ) : σ = τ := by
  have h1 : τ <+: σ := cone_subset_cone.mp (le_of_eq h)
  have h2 : σ <+: τ := cone_subset_cone.mp (le_of_eq h.symm)
  exact h2.eq_of_length (h2.length_le.antisymm h1.length_le)

/-- **`⊥` sits only in the cone of the empty prefix.** `⊥.mem(σΣ*) ↔ σ = Λ`: `⊥`'s only
neighbourhood is `Δ = ΛΣ*` (`cone_nil`), and a cone determines its prefix (`cone_injective`).
(Used by Exercise 2.17's base case, where `g(1)=⊥` is stated only at the input `⊥`.) -/
theorem bot_mem_cone_iff {σ : Str} : B.bot.mem (cone σ) ↔ σ = [] := by
  rw [mem_bot, B_master, ← cone_nil]
  constructor
  · exact cone_injective
  · intro h; rw [h]
end

end DomainTheory.NeighbourhoodSystems.ExampleB
end

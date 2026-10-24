module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example_1_5

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
/-- The system built by `ofPositive` is indeed positive. -/
theorem NeighborhoodSystem.ofPositive_isPositive {α : Type*} (mem : Set α → Prop)
    (master : Set α) (master_nonempty : master.Nonempty) (master_mem : mem master)
    (sub_master : ∀ {X : Set α}, mem X → X ⊆ master)
    (pos : ∀ ⦃X Y : Set α⦄, mem X → mem Y → (mem (X ∩ Y) ↔ (X ∩ Y).Nonempty)) :
    (NeighborhoodSystem.ofPositive mem master master_nonempty master_mem sub_master pos).IsPositive :=
  pos

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- The finite intersection is contained in each of its factors: `⋂_{i < n} Xᵢ ⊆ Xⱼ` for
`j < n`. (Supporting lemma: this is what makes `⋂_{i < n} Xᵢ` a common lower bound of the
sequence, the intuition behind consistency.) -/
theorem interUpTo_subset (X : ℕ → Set α) :
    ∀ {n j : ℕ}, j < n → V.interUpTo X n ⊆ X j := by
  intro n
  induction n with
  | zero => intro j h; exact absurd h (Nat.not_lt_zero j)
  | succ n ih =>
    intro j h
    rw [interUpTo_succ]
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp h) with h' | h'
    · subst h'; exact Set.inter_subset_right
    · exact Set.inter_subset_left.trans (ih h')


/-- **Theorem 1.1c (extension of the intersection property).** Scott: "from (ii), we can
extend the intersection property to any finite sequence." If `Xᵢ ∈ 𝒟` for every `i < n`
and the sequence is consistent, then the finite intersection `⋂_{i < n} Xᵢ` is again a
neighbourhood (`∈ 𝒟`). Proved by induction on `n`; the inductive step is one application of
condition (ii). -/
theorem interUpTo_mem (X : ℕ → Set α) :
    ∀ {n : ℕ}, (∀ i, i < n → V.mem (X i)) → V.Consistent X n →
      V.mem (V.interUpTo X n) := by
  intro n
  induction n with
  | zero => intro _ _; exact V.master_mem
  | succ n ih =>
    intro hX hcons
    obtain ⟨Z, hZmem, hZsub⟩ := hcons
    have hZsub' : Z ⊆ V.interUpTo X n ∩ X n := by rwa [interUpTo_succ] at hZsub
    -- The same witness `Z` shows the length-`n` prefix is consistent.
    have hconsn : V.Consistent X n :=
      ⟨Z, hZmem, hZsub'.trans Set.inter_subset_left⟩
    have hmemn : V.mem (V.interUpTo X n) :=
      ih (fun i hi => hX i (Nat.lt_succ_of_lt hi)) hconsn
    have hXn : V.mem (X n) := hX n (Nat.lt_succ_self n)
    rw [interUpTo_succ]
    exact V.inter_mem hmemn hXn hZmem hZsub'

/-- **Theorem 1.1c (consistency characterization).** "Consequently, `X₀, …, Xₙ₋₁` is
consistent in `𝒟` iff `⋂_{i < n} Xᵢ ∈ 𝒟`." (Given `Xᵢ ∈ 𝒟` for all `i < n`.)

* `→` is the extension property `interUpTo_mem`;
* `←` is immediate: the intersection is its own common lower bound. -/
theorem consistent_iff_interUpTo_mem (X : ℕ → Set α) {n : ℕ}
    (hX : ∀ i, i < n → V.mem (X i)) :
    V.Consistent X n ↔ V.mem (V.interUpTo X n) := by
  constructor
  · exact V.interUpTo_mem X hX
  · intro h; exact ⟨V.interUpTo X n, h, Set.Subset.refl _⟩


/-- A filter (`Element`) is closed under the finite intersection `⋂_{i<n} Xᵢ`: if every factor
`Xᵢ` (`i < n`) lies in the filter `x`, so does `interUpTo X n`. Used in Exercises 1.18 and 1.21.
Base case `x.master_mem`; inductive step one `x.inter_mem`. -/
theorem Element.mem_interUpTo {α : Type*} {V : NeighborhoodSystem α} (x : V.Element)
    (X : ℕ → Set α) :
    ∀ {n : ℕ}, (∀ i, i < n → x.mem (X i)) → x.mem (V.interUpTo X n) := by
  intro n
  induction n with
  | zero => intro _; exact x.master_mem
  | succ n ih =>
    intro h
    rw [interUpTo_succ]
    exact x.inter_mem (ih (fun i hi => h i (Nat.lt_succ_of_lt hi))) (h n (Nat.lt_succ_self n))

/-- Membership of the finite intersection in a filter, as a biconditional (given all factors
are neighbourhoods). `→` is upward closure along `interUpTo X n ⊆ Xᵢ` (`interUpTo_subset`); `←`
is `Element.mem_interUpTo`. -/
theorem Element.mem_interUpTo_iff {α : Type*} {V : NeighborhoodSystem α} (x : V.Element)
    (X : ℕ → Set α) {n : ℕ} (hX : ∀ i, i < n → V.mem (X i)) :
    x.mem (V.interUpTo X n) ↔ ∀ i, i < n → x.mem (X i) := by
  constructor
  · intro h i hi
    exact x.up_mem h (hX i hi) (V.interUpTo_subset X hi)
  · exact x.mem_interUpTo X


/- concordance: source L238 FACTOID 1.5b equivalent sequences same limit -/
/-- **Factoid 1.5b (Scott 1981, PRG-19).** "It is easy to prove that … the two families are
*equal* if and only if the sequences are *equivalent*." Given that every term of each sequence
is a neighbourhood, the limit families coincide exactly when the sequences are equivalent. -/
theorem limitFamily_eq_iff (X Y : ℕ → Set α)
    (hX : ∀ n, V.mem (X n)) (hY : ∀ m, V.mem (Y m)) :
    V.limitFamily X = V.limitFamily Y ↔ SeqEquiv X Y := by
  constructor
  · intro hEq
    refine ⟨fun m => ?_, fun n => ?_⟩
    · have hmem : Y m ∈ V.limitFamily Y := ⟨hY m, m, subset_rfl⟩
      rw [← hEq] at hmem
      obtain ⟨_, n, hn⟩ := hmem
      exact ⟨n, hn⟩
    · have hmem : X n ∈ V.limitFamily X := ⟨hX n, n, subset_rfl⟩
      rw [hEq] at hmem
      obtain ⟨_, m, hm⟩ := hmem
      exact ⟨m, hm⟩
  · rintro ⟨h1, h2⟩
    apply Set.ext
    intro Z
    constructor
    · rintro ⟨hZ, n, hn⟩
      obtain ⟨m, hm⟩ := h2 n
      exact ⟨hZ, m, hm.trans hn⟩
    · rintro ⟨hZ, m, hm⟩
      obtain ⟨n, hn⟩ := h1 m
      exact ⟨hZ, n, hn.trans hm⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Example15
section

open NeighborhoodSystem

/- concordance: source L210 FACTOID 1.5a consistent iff nonempty -/
/-- **Factoid 1.5a (Scott 1981, PRG-19).** In Example 1.5, "sets are consistent in `𝒟` iff they
have a non-empty intersection": a finite prefix `X₀, …, Xₙ₋₁` is consistent exactly when its
intersection `⋂_{i<n} Xᵢ` is non-empty. -/
theorem consistent_iff_inter_nonempty (X : ℕ → Set Token) (n : ℕ) :
    neighborhoodSystem.Consistent X n ↔ (neighborhoodSystem.interUpTo X n).Nonempty := by
  constructor
  · rintro ⟨Z, hZ, hsub⟩
    obtain ⟨z, hz⟩ := hZ
    exact ⟨z, hsub hz⟩
  · intro h
    exact ⟨_, h, subset_rfl⟩

/-- The neighbourhoods of Example 1.5 are exactly the non-empty subsets. -/
theorem mem_iff_nonempty (X : Set Token) : neighborhoodSystem.mem X ↔ X.Nonempty := Iff.rfl
end

end DomainTheory.NeighbourhoodSystems.Example15
end


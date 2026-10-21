/-ai
A set of elements is bounded if and only if every finite subset is bounded.

A bound of the whole set bounds every subset. Conversely, let C be the set of neighbourhoods that belong to some member of the given set. Each member of C is a neighbourhood by the subfamily law. Each term of a finite sequence from C belongs to some element of the set, and the chosen elements form a finite subset, which has a bound by hypothesis. That bound contains every term of the sequence and therefore their running intersection, so the running intersection is a neighbourhood contained in itself and witnesses finite consistency. The least filter of C then lies above every member of the set, because each neighbourhood of such a member belongs to C and hence to the least filter.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)








/-- **Exercise 1.27 — boundedness is finitary.** `X ⊆ |𝒟|` is bounded iff every *finite* subset
of `X` is bounded. The forward direction reuses any global bound. The reverse direction is the
content: assemble `C = ⋃_{x∈X} x` (the neighbourhoods of all members of `X`); `C` is finitely
consistent because any finite sequence drawn from `C` comes from finitely many members of `X`,
which form a finite subset, hence bounded — that bound's filter contains the whole finite
sequence, so its intersection lies in `𝒟`. The least filter `leastFilter C` (Exercise 1.18) is
then an upper bound of `X`. -/
theorem bounded_iff_finite_bounded (X : Set V.Element) :
    V.Bounded X ↔ ∀ S : Set V.Element, S ⊆ X → S.Finite → V.Bounded S := by
  constructor
  · rintro ⟨y, hy⟩ S hS _
    exact ⟨y, fun x hx => hy x (hS hx)⟩
  · intro hfin
    set C : Set (Set α) := {Z | ∃ x : V.Element, x ∈ X ∧ x.mem Z} with hCdef
    have hCsub : ∀ Z ∈ C, V.mem Z := by rintro Z ⟨x, _, hxZ⟩; exact x.sub hxZ
    have hCcons : V.FinitelyConsistent C := by
      intro n seq hseqC
      choose g hgX hgmem using hseqC
      set S : Set V.Element := Set.range (fun i : Fin n => g i.1 i.2) with hSdef
      have hSfin : S.Finite := Set.finite_range _
      have hSsub : S ⊆ X := by
        rintro _ ⟨i, rfl⟩
        exact hgX i.1 i.2
      obtain ⟨y, hy⟩ := hfin S hSsub hSfin
      have hseqy : ∀ i, i < n → y.mem (seq i) := by
        intro i hi
        have hle : g i hi ≤ y := hy _ ⟨⟨i, hi⟩, rfl⟩
        exact hle (seq i) (hgmem i hi)
      have hmem : y.mem (V.interUpTo seq n) := y.mem_interUpTo seq hseqy
      exact ⟨V.interUpTo seq n, y.sub hmem, subset_rfl⟩
    refine ⟨V.leastFilter C hCsub hCcons, ?_⟩
    intro x hx Z hZ
    exact V.subset_leastFilter C hCsub hCcons ⟨x, hx, hZ⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems

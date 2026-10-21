/-ai
If the encoding of a string σ is contained in the encoding of a string τ, then τ is a prefix of σ.

The encoding of σ is an iterate neighbourhood contained in both encodings, so the strings agree wherever both are defined, and therefore one is a prefix of the other. If σ is a prefix of τ and the lengths differ, then τ is strictly longer and has a bit at the length of σ. A token outside that bit neighbourhood lies in the encoding of σ, because σ is undefined there, but the inclusion would place it in the bit neighbourhood. Equal lengths turn the prefix into equality. The remaining alternative is already that τ is a prefix of σ.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.exists_not_mem_bitNbhd

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap
















/-- **Prefix recovery.** `encSet σ ⊆ encSet τ` forces `τ` to be an initial segment of `σ`. -/
theorem prefix_of_encSet_subset {σ τ : Str} (h : encSet σ ⊆ encSet τ) : τ <+: σ := by
  have hag : ∀ (i : ℕ) (b b' : Bool), σ[i]? = some b → τ[i]? = some b' → b = b' :=
    fun i b b' => encSet_agree (encSet_mem σ) subset_rfl h
  rcases comparable_of_agree hag with hστ | hτσ
  · by_cases hlen : σ.length = τ.length
    · exact (hστ.eq_of_length hlen) ▸ List.prefix_rfl
    · exfalso
      have hlt : σ.length < τ.length := lt_of_le_of_ne hστ.length_le hlen
      have hb' : τ[σ.length]? = some τ[σ.length] := List.getElem?_eq_getElem hlt
      obtain ⟨t, ht⟩ := exists_not_mem_bitNbhd τ[σ.length]
      have hmemσ : (σ.length, t) ∈ encSet σ := by
        intro b hb
        rw [List.getElem?_eq_none_iff.mpr (le_refl _)] at hb
        exact absurd hb (by simp)
      exact ht ((h hmemσ) _ hb')
  · exact hτσ

end DomainTheory.NeighbourhoodSystems.Exercise317

/-ai
If two maps are computable, their pairing into the product is computable.

Their relations are recursively enumerable. Reindex them by pairing the domain index with each half of the codomain index. The conjunction matches the paired relation: one direction drops product membership, and the other restores it from the two component neighbourhoods.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ α' β' : Type*}


variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Theorem 7.4 (Scott 1981, PRG-19) — the paired map `⟨f, g⟩` is computable.** `Zₙ ⟨f, g⟩ (X⁰_k ∪
X¹_l) ↔ Zₙ f X⁰_k ∧ Zₙ g X¹_l`, the conjunction of two r.e. relations. -/
theorem paired_isComputable {V₂ : NeighborhoodSystem γ}
    {P₂ : ComputablePresentation V₂} {P₀ : ComputablePresentation V₀}
    {P₁ : ComputablePresentation V₁} {a : ApproximableMap V₂ V₀} {b : ApproximableMap V₂ V₁}
    (ha : IsComputableMap P₂ P₀ a) (hb : IsComputableMap P₂ P₁ b) :
    IsComputableMap P₂ (prodPresentation P₀ P₁) (paired a b) := by
  have ha' : REPred (fun s => a.rel (P₂.X s.unpair.1) (P₀.X s.unpair.2)) := ha
  have hb' : REPred (fun s => b.rel (P₂.X s.unpair.1) (P₁.X s.unpair.2)) := hb
  have hra : Nat.Primrec (fun t => Nat.pair t.unpair.1 t.unpair.2.unpair.1) :=
    Nat.Primrec.left.pair (Nat.Primrec.left.comp Nat.Primrec.right)
  have hrb : Nat.Primrec (fun t => Nat.pair t.unpair.1 t.unpair.2.unpair.2) :=
    Nat.Primrec.left.pair (Nat.Primrec.right.comp Nat.Primrec.right)
  refine REPred.of_iff (fun t => ?_) ((ha'.comp hra).and (hb'.comp hrb))
  simp only [prodPresentation_X, paired_rel, inl_preimage_prodNbhd, inr_preimage_prodNbhd,
    unpair_pair_fst, unpair_pair_snd]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩,
    fun h => ⟨prod_mem_prodNbhd (P₀.mem_X _) (P₁.mem_X _), h.1, h.2⟩⟩

end DomainTheory.NeighbourhoodSystems

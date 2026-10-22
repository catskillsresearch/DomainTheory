module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funListOf
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funListOf_cons

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

/-- **Choice-free `rel_interYs` for a presented list.** Any `f ∈ stepFun (funListOf el)` relates each
`X₀_{n'}` to the intersection of the relevant outputs `interYs Δ₁ (funListOf el) (X₀_{n'})`. The
case split on `X₀_{n'} ⊆ X₀_{e.1}` is discharged by `P₀.incl_computable.em` (no `Classical.choice`). -/
theorem rel_interYs_funList {f : ApproximableMap V₀ V₁} {el : List ℕ}
    (hf : f ∈ stepFun (funListOf P₀ P₁ el)) (n' : ℕ) :
    f.rel (P₀.X n') (interYs V₁.master (funListOf P₀ P₁ el) (P₀.X n')) := by
  induction el with
  | nil =>
    rw [funListOf, List.map_nil, interYs_nil]
    exact f.mono f.master_rel (V₀.sub_master (P₀.mem_X n')) subset_rfl (P₀.mem_X n') V₁.master_mem
  | cons e el ih =>
    rw [funListOf_cons] at hf
    have hftail : f ∈ stepFun (funListOf P₀ P₁ el) :=
      fun p hp => hf p (List.mem_cons_of_mem _ hp)
    have htail := ih hftail
    rw [funListOf_cons]
    rcases P₀.incl_computable.em (Nat.pair n' e.unpair.1) with hinc | hinc <;>
      simp only [unpair_pair_fst, unpair_pair_snd] at hinc
    · have hp : f.rel (P₀.X e.unpair.1) (P₁.X e.unpair.2) :=
        hf (funPair P₀ P₁ e) (List.mem_cons.mpr (Or.inl rfl))
      have hXp2 : f.rel (P₀.X n') (P₁.X e.unpair.2) :=
        f.mono hp hinc subset_rfl (P₀.mem_X n') (f.rel_cod hp)
      have heq : interYs V₁.master (funPair P₀ P₁ e :: funListOf P₀ P₁ el) (P₀.X n')
          = P₁.X e.unpair.2 ∩ interYs V₁.master (funListOf P₀ P₁ el) (P₀.X n') := by
        rw [interYs_cons]; ext z
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, funPair]
        exact ⟨fun ⟨h1, h2⟩ => ⟨h1 hinc, h2⟩, fun ⟨h1, h2⟩ => ⟨fun _ => h1, h2⟩⟩
      rw [heq]; exact f.inter_right hXp2 htail
    · have heq : interYs V₁.master (funPair P₀ P₁ e :: funListOf P₀ P₁ el) (P₀.X n')
          = interYs V₁.master (funListOf P₀ P₁ el) (P₀.X n') := by
        rw [interYs_cons]; ext z
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, funPair]
        exact ⟨fun h => h.2, fun h => ⟨fun hc => absurd hc hinc, h⟩⟩
      rw [heq]; exact htail

end DomainTheory.NeighbourhoodSystems

/-ai
The first projection relates the sharp neighbourhood of index m to the sharp neighbourhood of index k if and only if k is 0, or m is even and nonzero and the sharp neighbourhood indexed by the left component of m/2 − 1 is contained in the sharp neighbourhood of index k.

Both enumerated sets are sharp neighbourhoods, so the relation reduces to its disjunction, and the codomain equals the master neighbourhood exactly when its index is 0. The shape of m has three cases. The index 0 enumerates the master neighbourhood, which is never a pair embedding, while the numerical side requires m to be nonzero. An odd index enumerates a zero-embedding, which is never a pair embedding, and an odd index is not divisible by 2. An even index of the form 2a + 2 enumerates the pair embedding of the two sharp neighbourhoods coded by a, and halving identifies a with the left-child index. Injectivity of pair embeddings matches the left component with the required inclusion, and the converse is that same pair decomposition.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)








/-- The index characterization of `proj0Map` against the `Vsharp` enumeration. `V_m proj₀ V_k` iff
`k = 0` (`V_k = Γ`) or `m` is an even node index `2a+2` with `V_{p a} ⊆ V_k` (the left child). -/
theorem proj0_rel_Vsharp_iff (P : ComputablePresentation D) (m k : ℕ) :
    (proj0Map hD).rel (Vsharp D P m) (Vsharp D P k) ↔
      k = 0 ∨ (m % 2 = 0 ∧ m ≠ 0 ∧ Vsharp D P (m / 2 - 1).unpair.1 ⊆ Vsharp D P k) := by
  rw [proj0Map_rel, and_iff_right (Vsharp_mem P m), and_iff_right (Vsharp_mem P k)]
  refine or_congr (Vsharp_eq_Gamma_iff P hD k) ?_
  rcases nat_shape m with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rw [Vsharp_zero]
    constructor
    · rintro ⟨Pp, Qq, heq, -⟩; exact absurd heq.symm (embPair_ne_Gamma D hD Pp Qq)
    · rintro ⟨-, hne, -⟩; exact absurd rfl hne
  · rw [Vsharp_odd]
    constructor
    · rintro ⟨Pp, Qq, heq, -⟩; exact absurd heq (embZero_ne_embPair D hD (P.mem_X a) Pp Qq)
    · rintro ⟨hmod, -, -⟩; exact absurd hmod (by omega)
  · rw [Vsharp_even, show (2 * a + 2) / 2 - 1 = a from by omega]
    constructor
    · rintro ⟨Pp, Qq, heq, hPk⟩
      obtain ⟨hP, -⟩ := embPair_injective heq
      exact ⟨by omega, by omega, by rw [hP]; exact hPk⟩
    · rintro ⟨-, -, hsub⟩
      exact ⟨Vsharp D P a.unpair.1, Vsharp D P a.unpair.2, rfl, hsub⟩

end Proposition77
end DomainTheory.NeighbourhoodSystems
